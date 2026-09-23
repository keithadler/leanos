#!/usr/bin/env python3
"""Runs the mutants test/mutants.sh lists, several at once.

Each worker has its own copy of the Lean project (a few MB, with the built dependencies,
so only the mutated kernel and what depends on it rebuild) in a temporary directory, and
takes the next mutant when it is done with one: the kernel in the working tree is never
touched. A mutant must compile (`lake build LeanOS.Kernel`); then the whole build, proofs
included, must fail.

Usage: mutants.sh | mutants.py [JOBS]   (records: name NUL from NUL to NUL)
"""
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECT = ["LeanOS.lean", "LeanOS", "lakefile.toml", "lake-manifest.json", "lean-toolchain", ".lake"]


def read_mutants():
    fields = sys.stdin.buffer.read().decode().split("\0")
    if fields and fields[-1] == "":
        fields.pop()
    assert len(fields) % 3 == 0, "a mutant needs a name, a target and a replacement"
    return [tuple(fields[i:i + 3]) for i in range(0, len(fields), 3)]


def lake(where, *target):
    return subprocess.run(["lake", "build", *target], cwd=where, stdout=subprocess.DEVNULL,
                          stderr=subprocess.DEVNULL).returncode == 0


def main():
    jobs = int(sys.argv[1]) if len(sys.argv) > 1 else max(1, (os.cpu_count() or 2) // 2)
    mutants = read_mutants()
    if os.environ.get("LIMIT"):                     # for timing the runner on a few
        mutants = mutants[:int(os.environ["LIMIT"])]
    kernel = open(os.path.join(ROOT, "LeanOS", "Kernel.lean")).read()
    if not lake(ROOT):
        print("FAIL: the unmutated kernel does not build")
        return 1
    base = tempfile.mkdtemp(prefix="leanos-mutants-")
    todo = queue.Queue()
    for i, m in enumerate(mutants):
        todo.put((i, m))
    results = [None] * len(mutants)
    lock = threading.Lock()
    t0 = time.monotonic()

    def worker(w):
        where = os.path.join(base, f"w{w}")
        os.makedirs(where)
        for item in PROJECT:
            src = os.path.join(ROOT, item)
            if os.path.isdir(src):
                shutil.copytree(src, os.path.join(where, item), symlinks=True)
            elif os.path.exists(src):
                shutil.copy2(src, where)
        path = os.path.join(where, "LeanOS", "Kernel.lean")
        while True:
            try:
                i, (name, frm, to) = todo.get_nowait()
            except queue.Empty:
                return
            if frm not in kernel:
                verdict = "BROKEN: %s (its target is no longer in Kernel.lean)" % name
            else:
                with open(path, "w") as f:
                    f.write(kernel.replace(frm, to, 1))
                if not lake(where, "LeanOS.Kernel"):
                    verdict = "BROKEN: %s (the mutated kernel does not compile)" % name
                elif lake(where):
                    verdict = "SURVIVED: %s" % name
                else:
                    verdict = "caught: %s" % name
            results[i] = verdict
            with lock:
                print(verdict, flush=True)

    threads = [threading.Thread(target=worker, args=(w,)) for w in range(min(jobs, len(mutants)))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    shutil.rmtree(base, ignore_errors=True)
    bad = [r for r in results if not r.startswith("caught")]
    took = time.monotonic() - t0
    if bad:
        print(f"FAIL: {len(bad)} of {len(mutants)} mutants not caught ({took:.0f} s, {jobs} at once)")
        return 1
    print(f"ok: all {len(mutants)} mutants were caught by the proofs ({took:.0f} s, {jobs} at once)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
