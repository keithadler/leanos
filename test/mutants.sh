#!/bin/bash
# Breaks the kernel on purpose, one way at a time, and checks the proofs reject each
# break. A mutant that still builds means a guarantee is weaker than it claims.
set -u
cd "$(dirname "$0")/.."
backup=$(mktemp)
cp LeanOS/Kernel.lean "$backup"
trap 'cp "$backup" LeanOS/Kernel.lean; rm -f "$backup"' EXIT

survived=0
mutant() {
  local name=$1 from=$2 to=$3
  cp "$backup" LeanOS/Kernel.lean
  if ! python3 - "$from" "$to" <<'PY'
import sys
p = 'LeanOS/Kernel.lean'
s = open(p).read()
if sys.argv[1] not in s:
    sys.exit(1)
open(p, 'w').write(s.replace(sys.argv[1], sys.argv[2], 1))
PY
  then
    echo "BROKEN: $name (its target is no longer in Kernel.lean)"; survived=1; return
  fi
  if lake build >/dev/null 2>&1; then
    echo "SURVIVED: $name"; survived=1
  else
    echo "caught: $name"
  fi
}

mutant "derive grants whatever is asked" \
  "⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩" "⟨o, Rights.ofBits bits, c.badge⟩"
mutant "derive lets a task pick its badge" \
  "⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩" "⟨o, c.rights.meet (Rights.ofBits bits), bits⟩"
mutant "level-2 table points past the 16 level-3 tables" \
  "def l2Word (l3 k : Nat) : Nat := if k < l3Tables then" "def l2Word (l3 k : Nat) : Nat := if k < l3Tables + 1 then"
mutant "map ignores the capability's frames" \
  "app (runMaps vpn base c.rights count)" "app (runMaps vpn (base + 1) c.rights count)"
mutant "derive cuts a piece past the end of the run" \
  "else if offset + count ≤ n then some (.frames (base + offset) count) else none" "else some (.frames (base + offset) count)"
mutant "map outside the user window" \
  "if vpn + count ≤ userPages && c.rights.r &&" "if c.rights.r &&"
mutant "write skips the page check" \
  "allReadable t.maps ((va - userBase) / pageSize)" "true || allReadable t.maps ((va - userBase) / pageSize)"
mutant "send without the send right" \
  "if c.rights.w then
        match grantOf" "if true then
        match grantOf"
mutant "receive without the receive right" \
  "if c.rights.r then
        match findSender" "if true then
        match findSender"
mutant "grant without the grant right" \
  "else if ep.rights.x then" "else if true then"
mutant "grant an endpoint capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | .frames _ _ => some (some g)
      | .endpoint _ => some (some g)
      | _ => none"
mutant "sender picks its own badge" \
  "let m : Msg := ⟨c.badge, w0, w1, w2, g, call⟩" "let m : Msg := ⟨w0, w0, w1, w2, g, call⟩"
mutant "reply wakes a task that is not waiting for it" \
  "    if awaitsFrom s.tasks j s.cur then" "    if true then"
mutant "reply hands over the replier's capabilities" \
  "ret (setTask s j { u with status := .ready, result := 0 :: w0 :: w1 :: w2 :: .nil }) t'" "ret (setTask s j { u with status := .ready, caps := t.caps, result := 0 :: w0 :: w1 :: w2 :: .nil }) t'"
mutant "manifest gives mallory the grant right" \
  "epCap 0 false true false 2" "epCap 0 false true true 2"
mutant "manifest gives mallory the receive right" \
  "epCap 0 false true false 2" "epCap 0 true true false 2"
mutant "map framebuffer frames without checking the firmware's address" \
  "(fbSane s.fbBase && base + count ≤ devBase)" "(base + count ≤ devBase)"
mutant "accept a framebuffer that overlaps the frame pool" \
  "b % pageSize == 0 && frameBase + poolFrames * pageSize ≤ b" "b % pageSize == 0 && frameBase ≤ b"
mutant "manifest gives mallory the framebuffer" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (runCap poolFrames fbPages Rights.rw)"
mutant "framebuffer frames count as alice's" \
  "if f < poolFrames then f / framesPerTask else if f < devBase then displayTask else inputTask" "if f < poolFrames then f / framesPerTask else if f < devBase then 0 else inputTask"
mutant "an interrupt wakes whoever waits on any line" \
  "    | .waitingIrq k => if k == n then some j else findIrqWaiter n ts (j + 1)" "    | .waitingIrq _ => some j"
mutant "manifest gives mallory the UART" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (runCap devBase devPages Rights.rw)"
mutant "manifest gives mallory the UART's interrupt" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (irqCap uartIrq)"
mutant "grant an interrupt capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | _ => some (some g)"
mutant "accept a framebuffer that overlaps the peripherals" \
  "b + fbPages * pageSize ≤ 0xFE000000" "b + fbPages * pageSize ≤ 2 ^ 36"
mutant "verify ignores the manifest" \
  "      if eqList h (expectedHash i) then setTask s i { t with status := .ready, hash := h }" "      if true then setTask s i { t with status := .ready, hash := h }"
mutant "tasks start ready, unchecked" \
  "def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .unverified, .nil, .nil, .nil⟩" "def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .ready, .nil, .nil, .nil⟩"
mutant "a stopped task may make system calls" \
  "    | .ready => runCall s t num a0 a1 a2 a3 a4
    | _ => ⟨s, 0, 0, false, 0⟩" "    | _ => runCall s t num a0 a1 a2 a3 a4"
mutant "user pages always executable" \
  "privNoExec + (if m.rights.x then 0 else userNoExec)" "privNoExec + 0"
mutant "read-only pages writable" \
  "(if m.rights.w then apUserRW else apUserRO)" "apUserRW"
mutant "kernel RAM executable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + shInner + accessFlag"
mutant "kernel RAM readable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + apUserRO + shInner + accessFlag + userNoExec"
mutant "scheduler may pick a waiting task" \
  "if isReady ts j then some j else findReady ts (j + 1) fuel" "some j"

cp "$backup" LeanOS/Kernel.lean
lake build >/dev/null 2>&1 || { echo "FAIL: the unmutated kernel no longer builds"; exit 1; }
[ $survived -eq 0 ] && echo "ok: every mutant was caught by the proofs" || exit 1
