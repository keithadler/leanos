#!/usr/bin/env python3
"""The kernel stack's worst case, argued from the code: the deepest the kernel stack can go,
from the frame of every function the image can run and the calls between them.

What it reads:
  build/leanos.elf   the kernel image as linked, whose code is what runs (llvm-objdump -d)
  build/stack/       every C file of the kernel compiled again with the shipped flags and
                     -fstack-usage (`make stackcheck`): clang writes each function's frame
                     size to NAME.su beside NAME.o

What it checks, failing (status 1) if any does not hold:
  - each object in build/stack/ has the same code and relocations as the shipped one, so the
    frame sizes are those of the code in the image;
  - every C function in the image has a frame size from clang, a static one (no alloca or
    variable-length array), and the stack adjustments in its code add up to that size;
  - every branch that leaves a function goes to the start of a function; every `br` is a
    jump table whose entries stay inside the function; every indirect call (`blr`) reaches
    only functions whose addresses the code puts in the register (traced back through the
    function), or is one of the ONCE functions, resolved the same way at each call;
  - no code in the image unmasks interrupts (writes DAIF), so interrupts never nest in the
    kernel, and arch/boot.S calls only the ENTRIES, each exception entry pushing FRAME_SIZE;
  - every cycle in the call graph is in RECURSION below, with a bound on how deep it goes;
  - the worst case, a kernel exception on top of the deepest entry, is at most BUDGET.

Then it prints the worst case and the path that reaches it, frame by frame.

Usage: tools/stackcheck.py [--verbose] [--self-test]
  --verbose    also lists the deepest functions
  --self-test  first checks the analysis fails on recursion missing from RECURSION and on an
               indirect call it cannot resolve (synthetic call graphs), then runs it
"""
import os
import re
import struct
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELF = os.path.join(ROOT, "build", "leanos.elf")
STACK = os.path.join(ROOT, "build", "stack")
LLVM = os.environ.get("LLVM") or next(
    (d for d in ("/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin") if os.path.isdir(d)), "/usr/bin")

# The kernel stack is 64 KiB per core (arch/kmain.c, STACK_SIZE). The bound must stay within
# half of it: the check fails long before the stack's guard would.
STACK_SIZE = 0x10000
BUDGET = STACK_SIZE // 2


def lean_def(name):
    """A constant of LeanOS/Kernel.lean: `def NAME : Nat := N`, or the length of a literal list."""
    with open(os.path.join(ROOT, "LeanOS", "Kernel.lean")) as f:
        src = f.read()
    m = re.search(rf"^def {name} : Nat := (\d+)$", src, re.M)
    if m:
        return int(m.group(1))
    m = re.search(rf"^def {name} : List Nat := (.*) :: \.nil$", src, re.M)
    if m:
        return m.group(1).count("::") + 1
    raise SystemExit(f"FAIL: no `def {name}` of the expected form in LeanOS/Kernel.lean")


# Recursion the kernel keeps: for each function in a cycle of the call graph, how many of its
# activations can be on the stack at once, and why. A cycle with a function not listed here
# fails the check, so new recursion must be bounded, and argued, before the kernel may have
# it. A walk over a list of n entries calls itself once for each entry and once more for the
# empty tail: n + 1 activations.
TASKS, CALLERS, LINES = lean_def("numTasks"), lean_def("maxCallers"), lean_def("irqLines")
RECURSION = {
    # the task list: state_bounded (LeanOS/Bounds.lean) proves len s.tasks = numTasks
    "lp_leanos_LeanOS_revokeAll": (TASKS + 1, f"`start` takes back slot k's frames from every task: "
                                   f"walks the task list, {TASKS} entries (state_bounded)"),
    "lp_leanos_LeanOS_wakeSleepers": (TASKS + 1, f"a timer tick wakes the sleepers whose time has come: "
                                      f"walks the task list, {TASKS} entries (state_bounded)"),
    "lp_leanos_LeanOS_mkTasksFrom": (TASKS + 1, f"`init` builds the task list, once at boot: "
                                     f"mkTasksFrom 0 numTasks, {TASKS} deep"),
    "lp_leanos_LeanOS_setNth___redArg": (TASKS + 1, f"replaces one entry of the task list ({TASKS}), a "
                                         f"task's reply slots (at most {CALLERS}) or a USB shadow list "
                                         f"(8): state_bounded; it stops at the entry, or at the end"),
    # a task's reply slots: task_bounded (LeanOS/Bounds.lean), len t.callers <= maxCallers
    "lp_leanos_LeanOS_placeCaller": (CALLERS + 1, f"a call takes the first free reply slot of the "
                                     f"receiver: at most {CALLERS} (task_bounded)"),
    "lp_leanos_LeanOS_forgetCaller": (CALLERS + 1, f"`start` drops the replies owed to the slot: "
                                      f"walks a task's reply slots, at most {CALLERS} (task_bounded)"),
    # the pending interrupt lines: state_bounded, len s.pending <= len irqLines
    "lp_leanos_LeanOS_dropLine": (LINES + 1, f"an interrupt wait takes its line off the pending list: "
                                  f"at most {LINES} entries, one per line of irqLines (state_bounded)"),
    # Not recursion at run time: kpanic draws the panic screen, which asks Lean for the
    # screen's size; leanos_fb_width and leanos_fb_height drop their argument, and could free
    # it (lean_dec_ref_cold, which can panic), but kpanic passes lean_box(0), a scalar, which
    # is never freed. So each is on the stack at most once along this cycle.
    "kpanic": (1, "draws the panic screen; its size queries are given a scalar, never freed"),
    "leanos_fb_width": (1, "kpanic passes lean_box(0): it never reaches lean_dec_ref_cold"),
    "leanos_fb_height": (1, "kpanic passes lean_box(0): it never reaches lean_dec_ref_cold"),
    "lean_dec_ref_cold": (1, "can stop the machine (kpanic), which never frees anything"),
}

# Functions that call through their third argument, `init` (x2): the runtime's one-time
# initialization of closed terms (rt/runtime.c, lean_obj_once_cold and the ONCE macro).
# Their own `blr x2` is resolved at each call instead: the caller's x2 must be traced back to
# function addresses, and the call counts as a call of the once function and then of `init`.
ONCE = {"lean_obj_once_cold", "lean_uint8_once_cold", "lean_uint16_once_cold",
        "lean_uint32_once_cold", "lean_uint64_once_cold", "lean_usize_once_cold"}

# What runs on a kernel stack, and how it gets there (arch/boot.S):
#   _start -> kmain                 core 0 at boot, sp = __stack_top
#   secondary -> secondary_main     cores 1-3, sp = core_stack_top[core]
#   vectors -> trap_common -> trap  every exception, below the FRAME_SIZE bytes of registers
#                                   the vector saved
# enter_user and restore leave the kernel, which puts sp back at the top of the stack.
ENTRIES = ("kmain", "secondary_main", "trap")
# The one assembly routine C may call: it sets sp to the top of the stack, less a frame, and
# returns to user mode (it never returns to its caller).
LEAVES_KERNEL = {"enter_user"}

CALLER_SAVED = {f"x{n}" for n in range(19)} | {"x30"}
RESOLVED = []            # (function, address, register, targets) of each indirect call


class Fail(Exception):
    pass


def fail(msg):
    raise Fail(msg)


def run(*args):
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        fail(f"{' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def frame_size_define():
    """FRAME_SIZE from arch/boot.S: what each exception entry pushes before it calls trap."""
    with open(os.path.join(ROOT, "arch", "boot.S")) as f:
        m = re.search(r"^#define FRAME_SIZE (\d+)$", f.read(), re.M)
    if not m:
        fail("no FRAME_SIZE in arch/boot.S")
    return int(m.group(1))


# ---------- the analysis build, and clang's frame sizes ----------

def analysis_objects():
    """Each object of the analysis build, with the shipped object it must match: build/NAME.o,
    or build/c/NAME.o for the standard library's modules (Init_*)."""
    pairs = []
    for d, _, files in os.walk(STACK):
        for f in sorted(files):
            if f.endswith(".o"):
                rel = os.path.relpath(os.path.join(d, f), STACK)
                sub = "c" if rel.startswith("Init_") else ""
                pairs.append((rel, os.path.join(d, f), os.path.join(ROOT, "build", sub, rel)))
    if not pairs:
        fail("no objects in build/stack (`make stackcheck` builds them)")
    return pairs


def code_of(path):
    """An object's code and relocations, as the disassembler shows them."""
    out = run(f"{LLVM}/llvm-objdump", "-d", "-r", "--no-show-raw-insn", path)
    return out.split("\n", 2)[2]     # the first lines name the file


def read_su(path):
    """clang's -fstack-usage output: `file:line:function<TAB>bytes<TAB>static|dynamic[,bounded]`."""
    frames = {}
    with open(path) as f:
        for line in f:
            where, size, kind = line.rstrip("\n").split("\t")
            name = where.rsplit(":", 1)[1]
            if name in frames and frames[name] != (int(size), kind):
                fail(f"{path}: two frame sizes for {name}")
            frames[name] = (int(size), kind)
    return frames


# ---------- the image: symbols and code ----------

class Func:
    def __init__(self, name, start, size, asm, frame=0):
        self.name, self.start, self.end, self.asm, self.frame = name, start, start + size, asm, frame
        self.insns = []          # (address, mnemonic, operand text)
        self.calls = set()       # the names of what it calls, or jumps to when it leaves
        self.preds = None


def elf_symbols():
    """The image's code symbols: C functions (FUNC, with the source file of a local one) and
    the assembly's labels (NOTYPE, in the code section)."""
    syms, file, text = [], None, None
    for line in run(f"{LLVM}/llvm-readelf", "-S", "--wide", ELF).splitlines():
        m = re.match(r"\s*\[\s*(\d+)\]\s+\.text\s", line)
        if m:
            text = m.group(1)
    for line in run(f"{LLVM}/llvm-readelf", "-s", "--wide", ELF).splitlines():
        p = line.split()
        if len(p) < 8 or not p[0].rstrip(":").isdigit():
            continue
        value, size, typ, bind, ndx, name = int(p[1], 16), int(p[2]), p[3], p[4], p[6], p[7]
        if typ == "FILE":
            file = name
        elif typ == "FUNC":
            syms.append((name, value, size, False, file if bind == "LOCAL" else None))
        elif typ == "NOTYPE" and ndx == text and not name.startswith("$"):
            syms.append((name, value, 0, True, None))
    return syms


INSN = re.compile(r"^\s*([0-9a-f]+):\s+(\S+)(?:\s+(.*?))?\s*$")
LABEL = re.compile(r"^([0-9a-f]+) <(.+)>:$")
TARGET = re.compile(r"0x([0-9a-f]+)(?: <[^>]*>)?")


def disassemble(by_start):
    out = run(f"{LLVM}/llvm-objdump", "-d", "--no-show-raw-insn", "--section=.text", ELF)
    cur = None
    for line in out.splitlines():
        m = LABEL.match(line)
        if m:
            cur = by_start.get(int(m.group(1), 16))
            if cur is None:
                fail(f"code at {m.group(2)} belongs to no known symbol")
            continue
        m = INSN.match(line.replace("\t", " "))
        if m and cur is not None:
            cur.insns.append((int(m.group(1), 16), m.group(2), (m.group(3) or "").split("//")[0].strip()))


def operands(s):
    """Split an operand list at the commas outside brackets."""
    ops, depth, tok = [], 0, ""
    for ch in s:
        depth += (ch == "[") - (ch == "]")
        if ch == "," and depth == 0:
            ops.append(tok.strip())
            tok = ""
        else:
            tok += ch
    if tok.strip():
        ops.append(tok.strip())
    return ops


def imm(tok):
    tok = tok.lstrip("#")
    return int(tok, 16) if tok.lower().startswith(("0x", "-0x")) else int(tok)


def addr_of(tok):
    m = TARGET.search(tok)
    return int(m.group(1), 16) if m else None


def code_frame(f):
    """The bytes a function's code takes off the stack pointer: every `sub sp, sp, #n` and
    every pre-indexed store to [sp, #-n]!. Any other kind of write to sp fails."""
    total = 0
    for addr, mn, ops_s in f.insns:
        ops = operands(ops_s)
        if not ops:
            continue
        if mn == "sub" and ops[:2] == ["sp", "sp"]:
            if not ops[2].startswith("#"):
                fail(f"{f.name}: the stack pointer moves by a register at {addr:#x} ({mn} {ops_s})")
            total += imm(ops[2]) << (int(ops[3].split("#")[1]) if len(ops) > 3 else 0)
        elif mn.startswith("st") and ops_s.endswith("]!") and "[sp, #-" in ops_s:
            total -= imm(ops_s.rsplit("[sp, ", 1)[1].rstrip("]!"))
        elif (mn == "add" and ops[:2] == ["sp", "sp"]) or (mn == "mov" and ops == ["sp", "x29"]):
            pass                                      # the epilogue gives it back
        elif mn.startswith("ld") and "[sp], #" in ops_s:
            pass                                      # the same, post-indexed
        elif ops[0] == "sp" or "[sp, #-" in ops_s and ops_s.endswith("]!"):
            fail(f"{f.name}: the stack pointer is written at {addr:#x} ({mn} {ops_s})")
    return total


BRANCHES = {"b", "bl", "cbz", "cbnz", "tbz", "tbnz"}
STOPS = {"b", "br", "ret", "eret"}       # no fall-through to the next instruction


def branch_target(mn, ops_s):
    if mn in BRANCHES or mn.startswith("b."):
        return addr_of(operands(ops_s)[-1])
    return None


def writes(mn, ops, reg):
    """Whether the instruction may change register `reg` (an x register, or its w half)."""
    names = (reg, "w" + reg[1:])
    if mn in ("bl", "blr"):
        return reg in CALLER_SAVED
    if mn.startswith(("stxr", "stlxr", "stxp", "stlxp")):
        return ops[0] in names                        # the status register
    for k, o in enumerate(ops):
        for n in names:
            if (o.startswith(f"[{n},") and o.endswith("]!")) or (o == f"[{n}]" and k + 1 < len(ops)):
                return True                           # a base register written back
    if mn.startswith(("st", "cmp", "cmn", "tst", "prfm", "dmb", "dsb", "isb", "msr", "hint", "nop")) or \
            mn in STOPS or mn in BRANCHES or mn.startswith("b."):
        return False
    pair = mn in ("ldp", "ldnp", "ldpsw", "ldxp", "ldaxp")
    return any(o in names for o in ops[:2 if pair else 1])


def elf_bytes(addr, n):
    """n bytes of the image at a virtual address (from its section headers)."""
    with open(ELF, "rb") as f:
        data = f.read()
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", data, 0x3a)
    for i in range(shnum):
        sh = struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize)
        typ, sh_addr, off, size = sh[1], sh[3], sh[4], sh[5]
        if typ == 1 and sh_addr <= addr and addr + n <= sh_addr + size:   # PROGBITS
            return data[off + addr - sh_addr: off + addr - sh_addr + n]
    fail(f"no section holds {addr:#x}")


def jump_table(f, i):
    """The targets of the `br` at index i, if it is clang's jump table: after a bounds check
    (cmp xI, #K; b.hi), adr of the table, adr of an anchor, a byte or halfword entry, and
    `add xN, anchor, entry, lsl #2`. None if it is not."""
    ins = f.insns
    if i < 4:
        return None
    reg = operands(ins[i][2])[0]
    (_, add, add_s), (_, ld, ld_s), (_, adr2, anc_s), (_, adr1, tab_s) = ins[i - 1], ins[i - 2], ins[i - 3], ins[i - 4]
    add_o, ld_o, anc_o, tab_o = operands(add_s), operands(ld_s), operands(anc_s), operands(tab_s)
    if not (add == "add" and add_o[:2] == [reg, reg] and add_o[3:] == ["lsl #2"]
            and ld in ("ldrb", "ldrh") and add_o[2] == "x" + ld_o[0][1:]
            and adr2 == "adr" and anc_o[0] == reg and adr1 == "adr" and ld_o[1].startswith("[" + tab_o[0] + ",")):
        return None
    index = ld_o[1].split(",")[1].strip().rstrip("]").split()[0]
    bound = None
    for k in range(i - 5, max(0, i - 10) - 1, -1):
        mn, o = ins[k][1], operands(ins[k][2])
        if mn == "cmp" and o[0] == index and o[1].startswith("#") and ins[k + 1][1] in ("b.hi", "b.hs"):
            bound = imm(o[1]) - (ins[k + 1][1] == "b.hs")
            break
    if bound is None:
        return None
    width = 1 if ld == "ldrb" else 2
    anchor, table = addr_of(anc_o[1]), addr_of(tab_o[1])
    raw = elf_bytes(table, (bound + 1) * width)
    return [anchor + 4 * int.from_bytes(raw[k * width:(k + 1) * width], "little") for k in range(bound + 1)]


def predecessors(f):
    """For each instruction, the instructions that can run just before it in f."""
    if f.preds is not None:
        return f.preds
    index = {a: k for k, (a, _, _) in enumerate(f.insns)}
    preds = [[] for _ in f.insns]
    for k, (a, mn, s) in enumerate(f.insns):
        if k + 1 < len(f.insns) and mn not in STOPS:
            preds[k + 1].append(k)
        targets = [branch_target(mn, s)] if mn != "br" else (jump_table(f, k) or [])
        for t in targets:
            if t is not None and t in index and mn != "bl":
                preds[index[t]].append(k)
    f.preds = preds
    return preds


def reaching(f, i, reg, by_start):
    """The functions register `reg` can hold when instruction i of f runs: traced back
    through f's code to where it is set (adr, or adrp and add, of a function; mov and csel
    are followed). None if any path sets it some other way, or brings it in from f's caller."""
    preds = predecessors(f)
    found, seen, work = set(), set(), [(i, reg)]
    while work:
        k, r = work.pop()
        if k == 0 or not preds[k]:
            return None                               # f's entry: the caller's value
        for p in preds[k]:
            if (p, r) in seen:
                continue
            seen.add((p, r))
            addr, mn, s = f.insns[p]
            o = operands(s)
            if not writes(mn, o, r):
                work.append((p, r))
                continue
            a = None
            if mn == "adr" and o[0] == r:
                a = addr_of(o[1])
            elif mn == "add" and o[:2] == [r, r] and len(o) == 3 and o[2].startswith("#") and \
                    preds[p] == [p - 1] and f.insns[p - 1][1] == "adrp" and operands(f.insns[p - 1][2])[0] == r:
                a = addr_of(operands(f.insns[p - 1][2])[1]) + imm(o[2])
            elif mn == "mov" and o[0] == r and o[1].startswith("x"):
                work.append((p, o[1]))
                continue
            elif mn == "csel" and o[0] == r:
                work += [(p, o[1]), (p, o[2])]
                continue
            g = by_start.get(a)
            if g is None or g.asm:
                return None
            found.add(g.name)
    return found


# ---------- the call graph ----------

def load():
    """The image's functions, with their frames and what each calls."""
    su_by_file, global_src = {}, {}
    for rel, obj, shipped in analysis_objects():
        if not os.path.exists(shipped):
            fail(f"build/stack/{rel} has no shipped object {os.path.relpath(shipped, ROOT)}")
        if code_of(obj) != code_of(shipped):
            fail(f"build/stack/{rel} and {os.path.relpath(shipped, ROOT)} differ in code, so the "
                 f"frame sizes would not be the image's (the two builds' flags must match)")
        su = obj[:-2] + ".su"
        if not os.path.exists(su):
            fail(f"no {os.path.relpath(su, ROOT)} (is it compiled with -fstack-usage?)")
        src = os.path.basename(rel)[:-2] + ".c"
        if src in su_by_file:
            fail(f"two objects compiled from files named {src}")
        su_by_file[src] = read_su(su)
        for line in run(f"{LLVM}/llvm-nm", "--defined-only", obj).splitlines():
            p = line.split()
            if len(p) == 3 and p[1] == "T":
                global_src[p[2]] = src

    funcs, by_start = {}, {}
    for name, value, size, asm, file in elf_symbols():
        if value in by_start:
            if not by_start[value].asm or not asm:
                fail(f"{name} and {by_start[value].name} are the same code")
            continue
        f = Func(name, value, size, asm)
        if not asm:
            src = file or global_src.get(name)
            if src not in su_by_file:
                fail(f"{name} ({src or 'no source file'}) is in the image, but no .su file covers it")
            if name not in su_by_file[src]:
                fail(f"{name}: clang gave no frame size for it in {src}")
            f.frame, how = su_by_file[src][name]
            if how != "static":
                fail(f"{name} ({src}) has a {how} frame (alloca or a variable-length array): "
                     f"its size is not fixed")
        if name in funcs:
            fail(f"two functions named {name} in the image")
        funcs[name] = f
        by_start[value] = f
    starts = sorted(by_start)
    for k, a in enumerate(starts):                    # an assembly label runs to the next symbol
        if by_start[a].asm:
            by_start[a].end = starts[k + 1] if k + 1 < len(starts) else a
    disassemble(by_start)
    for f in list(funcs.values()):
        edges(f, funcs, by_start)
    for name, f in funcs.items():                     # a once call runs the once function too
        if "->" in name:
            f.calls |= funcs[name.split("->")[0]].calls
    return funcs


def edges(f, funcs, by_start):
    if not f.asm:
        own = code_frame(f)
        if own != f.frame:
            fail(f"{f.name}: clang says its frame is {f.frame} bytes, its code takes {own}")
    for i, (addr, mn, s) in enumerate(f.insns):
        if mn == "msr" and "daif" in s.lower():
            fail(f"{f.name} writes DAIF at {addr:#x}: an interrupt could nest in the kernel")
        t = branch_target(mn, s)
        if t is not None:
            if f.start <= t < f.end and mn != "bl":
                continue                              # inside the function
            g = by_start.get(t)
            if g is None:
                fail(f"{f.name} branches at {addr:#x} into the middle of other code ({t:#x})")
            if g.asm and not f.asm and g.name not in LEAVES_KERNEL:
                fail(f"{f.name} calls {g.name} in arch/boot.S, which the check does not model")
            if g.name in ONCE:
                inits = reaching(f, i, "x2", by_start)
                if not inits:
                    fail(f"{f.name} calls {g.name} at {addr:#x} with an init (x2) the check cannot trace")
                RESOLVED.append((f.name, addr, "x2", sorted(inits)))
                for init in inits:
                    node = f"{g.name}->{init}"
                    if node not in funcs:
                        funcs[node] = Func(node, 0, 0, False, g.frame)
                        funcs[node].calls = {init}
                    f.calls.add(node)
            else:
                f.calls.add(g.name)
        elif mn == "blr":
            if f.name in ONCE:
                continue                              # resolved at each call
            reg = operands(s)[0]
            targets = reaching(f, i, reg, by_start)
            if not targets:
                fail(f"{f.name} makes an indirect call at {addr:#x} (blr {reg}) to what the check "
                     f"cannot trace")
            f.calls |= targets
            RESOLVED.append((f.name, addr, reg, sorted(targets)))
        elif mn == "br":
            if f.asm:
                fail(f"{f.name} (arch/boot.S) jumps through a register at {addr:#x}")
            targets = jump_table(f, i)
            if targets is None:
                fail(f"{f.name} jumps through a register at {addr:#x} (br {s}), not by a jump table")
            outside = [t for t in targets if not f.start <= t < f.end]
            if outside:
                fail(f"{f.name}: the jump table at {addr:#x} leads out of the function, to {outside[0]:#x}")


def check_boot_s(funcs, frame_size):
    """arch/boot.S calls only the ENTRIES, and every exception entry pushes FRAME_SIZE."""
    called = set()
    by_start = {f.start: f for f in funcs.values() if f.end > f.start}
    for f in funcs.values():
        if not f.asm:
            continue
        for addr, mn, s in f.insns:
            o = operands(s)
            if mn == "bl":
                called.add(by_start[branch_target(mn, s)].name)
            elif mn == "blr":
                fail(f"{f.name} (arch/boot.S) calls through a register at {addr:#x}")
            elif mn == "sub" and o[:2] == ["sp", "sp"] and imm(o[2]) != frame_size:
                fail(f"{f.name} (arch/boot.S) pushes {imm(o[2])} bytes, not FRAME_SIZE = {frame_size}")
    if called != set(ENTRIES):
        fail(f"arch/boot.S calls {sorted(called)}, but ENTRIES has {sorted(ENTRIES)}")


# ---------- depth ----------

def sccs(funcs, roots):
    """The strongly connected components of what the roots reach (Tarjan), callees first."""
    index, low, on, stack, out = {}, {}, set(), [], []
    sys.setrecursionlimit(max(10000, 4 * len(funcs)))

    def visit(v):
        index[v] = low[v] = len(index)
        stack.append(v)
        on.add(v)
        for w in sorted(funcs[v].calls):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))
    for r in roots:
        if r not in funcs:
            fail(f"entry {r} is not in the image")
        if r not in index:
            visit(r)
    return out


def depths(funcs, roots, recursion):
    """The deepest stack each reachable function can use, its own frame included: a cycle's
    frames times its bound, then the deepest of what the cycle calls outside itself."""
    depth, deeper, comp_of, unlisted = {}, {}, {}, []
    for comp in sccs(funcs, roots):
        members = set(comp)
        times = 1
        if len(comp) > 1 or comp[0] in funcs[comp[0]].calls:
            missing = [m for m in comp if m not in recursion]
            if missing:
                unlisted.append(" <-> ".join(comp) + (f" (unlisted: {', '.join(missing)})" if len(comp) > 1 else ""))
            else:
                times = max(recursion[m][0] for m in comp)
        below = max(((depth[w], w) for m in comp for w in funcs[m].calls if w not in members),
                    default=(0, None))
        for m in comp:
            depth[m] = times * sum(funcs[n].frame for n in comp) + below[0]
            deeper[m] = below[1]
            comp_of[m] = (comp, times)
    if unlisted:
        fail("recursion not in RECURSION (tools/stackcheck.py): " + "; ".join(unlisted))
    return depth, deeper, comp_of


def analyze(funcs, frame_size, recursion):
    depth, deeper, comp_of = depths(funcs, ENTRIES, recursion)
    from_user = frame_size + depth["trap"]
    deepest = max(depth["kmain"], depth["secondary_main"], from_user)
    # A kernel exception (synchronous, SError or FIQ; interrupts stay masked) can come at the
    # deepest point: one more frame and trap, which stops the machine (kind >= 2). That path
    # is taken to be as deep as any of trap's.
    worst = deepest + frame_size + depth["trap"]
    return depth, deeper, comp_of, from_user, worst


def report(funcs, frame_size, recursion, verbose=False):
    check_boot_s(funcs, frame_size)
    depth, deeper, comp_of, from_user, worst = analyze(funcs, frame_size, recursion)
    code = [f.name for f in funcs.values() if not f.asm and "->" not in f.name and f.name not in ONCE]
    unseen = sorted(n for n in code if n not in depth)
    if unseen:
        fail(f"{len(unseen)} functions in the image are not reached from {', '.join(ENTRIES)}, so "
             f"something calls them in a way the check does not see: {', '.join(unseen[:5])}")
    print(f"stackcheck: all {len(code) + len(ONCE)} C functions in the image, reached from "
          f"{', '.join(ENTRIES)}")
    once = [r for r in RESOLVED if r[2] == "x2"]
    print(f"  indirect calls: {len(once)} calls of the runtime's once functions, each with its init "
          f"traced ({len({t for r in once for t in r[3]})} inits)")
    for name, addr, reg, targets in RESOLVED:
        if reg != "x2":
            print(f"  indirect call: {name} at {addr:#x}, blr {reg}: {', '.join(targets)}")
    cycles = sorted({tuple(c) for c, t in comp_of.values() if len(c) > 1 or c[0] in funcs[c[0]].calls})
    for c in cycles:
        print(f"  recursion {' <-> '.join(c)}: {sum(funcs[m].frame for m in c)} bytes, "
              f"at most {max(recursion[m][0] for m in c)} deep")
    print(f"  kmain, core 0 at boot:                {depth['kmain']:6} bytes")
    print(f"  secondary_main, cores 1-3 at boot:    {depth['secondary_main']:6} bytes")
    print(f"  an exception from user mode:          {from_user:6} bytes "
          f"({frame_size} saved by arch/boot.S, {depth['trap']} from trap down)")
    print(f"  and a kernel exception on top of it:  {worst:6} bytes")
    start = "trap" if from_user >= max(depth["kmain"], depth["secondary_main"]) else \
        max(("kmain", "secondary_main"), key=lambda n: depth[n])
    print(f"  the deepest path, from {start}:")
    if start == "trap":
        print(f"    {frame_size:6}  the registers arch/boot.S saves")
    v = start
    while v is not None:
        comp, times = comp_of[v]
        own = sum(funcs[m].frame for m in comp)
        name = comp[0] if len(comp) == 1 else "{" + ", ".join(comp) + "}"
        print(f"    {own * times:6}  {name}" + (f" ({own} x {times})" if times > 1 else ""))
        v = deeper[v]
    if verbose:
        print("  the deepest functions (from the function down, its own frame):")
        for name in sorted(depth, key=lambda n: -depth[n])[:40]:
            print(f"    {depth[name]:6} {funcs[name].frame:5}  {name}")
    if worst > BUDGET:
        fail(f"the kernel stack can reach {worst} bytes, over the budget of {BUDGET} "
             f"(half of the {STACK_SIZE // 1024} KiB stack)")
    print(f"ok: the kernel stack's worst case is {worst} bytes, within the budget of {BUDGET} "
          f"(half of the {STACK_SIZE // 1024} KiB stack)")
    return worst


def self_test(funcs, frame_size):
    """The analysis must reject what it cannot bound. Each case here must fail (or, for the
    last two, give the right answer); then the real analysis runs."""
    resolved = len(RESOLVED)
    def expect_fail(what, words, thunk):
        try:
            thunk()
        except Fail as e:
            if words not in str(e):
                raise
        else:
            fail(f"self-test: {what} was not caught")

    def graph(calls):
        fs = {}
        for name in set(calls) | {w for ws in calls.values() for w in ws}:
            fs[name] = Func(name, 0, 0, False, 16)
            fs[name].calls = set(calls.get(name, ()))
        return fs

    # recursion missing from the table: in the image (revokeAll), and made up
    expect_fail("the image's revokeAll without its bound", "lp_leanos_LeanOS_revokeAll",
                lambda: analyze(funcs, frame_size, {k: v for k, v in RECURSION.items()
                                                    if k != "lp_leanos_LeanOS_revokeAll"}))
    base = {"kmain": ["a"], "secondary_main": [], "trap": ["b"], "a": [], "b": ["c"], "c": []}
    for cycle in ({"c": ["b"]}, {"c": ["c"]}):
        expect_fail(f"an unlisted recursion {cycle}", "not in RECURSION",
                    lambda: analyze(graph({**base, **cycle}), 288, {}))
    worst = analyze(graph({**base, "c": ["b"]}), 288, {"b": (5, ""), "c": (5, "")})[4]
    if worst != 2 * (288 + 16 + 5 * 32):
        fail(f"self-test: a listed recursion of 5 gave {worst} bytes")

    # indirect calls: through a register loaded from memory, or one a call may have changed
    def code(*insns):
        f = Func("f", 0x1000, 4 * len(insns), False)
        f.insns = [(0x1000 + 4 * k, mn, ops) for k, (mn, ops) in enumerate(insns)]
        g, h = Func("g", 0x2000, 4, False), Func("h", 0x3000, 4, False)
        once = Func("lean_obj_once_cold", 0x4000, 4, False)
        edges(f, {}, {0x1000: f, 0x2000: g, 0x3000: h, 0x4000: once})
        return f.calls
    expect_fail("a call through a loaded pointer", "cannot trace",
                lambda: code(("ldr", "x8, [x0]"), ("blr", "x8"), ("ret", "")))
    expect_fail("a call through a register a call changed", "cannot trace",
                lambda: code(("adr", "x8, 0x2000 <g>"), ("bl", "0x3000 <h>"), ("blr", "x8"), ("ret", "")))
    expect_fail("a once call with an unknown init", "cannot trace",
                lambda: code(("mov", "x2, x0"), ("bl", "0x4000 <lean_obj_once_cold>"), ("ret", "")))
    got = code(("adr", "x10, 0x2000 <g>"), ("adr", "x11, 0x3000 <h>"), ("cmp", "x0, #0x8"),
               ("csel", "x28, x10, x11, ne"), ("bl", "0x3000 <h>"), ("blr", "x28"), ("ret", ""))
    if got != {"g", "h"}:
        fail(f"self-test: a pointer chosen by csel traced to {sorted(got)}")
    del RESOLVED[resolved:]
    print("stackcheck: self-test ok (unlisted recursion, untraceable indirect calls: caught)")


def main():
    try:
        funcs, frame_size = load(), frame_size_define()
        if "--self-test" in sys.argv:
            self_test(funcs, frame_size)
        report(funcs, frame_size, RECURSION, "--verbose" in sys.argv)
    except Fail as e:
        print(f"FAIL: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
