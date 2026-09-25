#!/usr/bin/env python3
"""Runs the tests `make test` runs, several at once.

Each test gets a folder of its own, build/test/NAME (LEANOS_TEST_DIR: its SD card, its screen
captures, its tampered kernel), so no two tests share a file. What a test prints goes to
build/test/NAME/output.txt and is shown whole when the test ends, never mixed with another's;
then a table of every test and how long it took. The longest tests start first.

net, web and timezone start servers on the host for leanos to reach, so they run one after
the other, never beside each other. crash cuts the power on CRASH_LANES cards at once (test/crash.sh)
and counts for that many.

Usage: test/all.py [TEST...]   (default: all of them; exit status 1 if any fails)
  JOBS=N   at most N tests (QEMUs) at once; default half the cores, at most 4. JOBS=1 runs
           them one after the other, as `make test` used to, crash on a single card.
"""
import os
import shutil
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "build", "test")

# Every test, in the order `make test` ran them, and about how long each takes alone
# (seconds, on a 10-core Mac), to start the longest first.
TESTS = {"boot": 4, "apps": 31, "programs": 25, "power": 8, "piimage": 3, "tamper": 8, "fuzz": 64,
         "usb": 6, "touch": 5, "crash": 245, "bigprog": 14, "stack": 15, "stackcheck": 5, "edit": 9, "net": 23,
         "kill": 7, "web": 14, "timezone": 25, "clipboard": 14, "term-history": 14,
         "chaos": 50}
# Tests that must not overlap: each group runs as one chain, in this order.
CHAINS = [("net", "web", "timezone")]


def default_jobs():
    # a busy QEMU takes more than one core (four emulated cores, and its I/O), and drawing-
    # speed checks measure host time: half the cores, and no more than four
    return max(1, min(4, (os.cpu_count() or 2) // 2))


class Unit:
    """One test, or a chain of tests run one after the other, and the slots it takes."""

    def __init__(self, names, jobs):
        self.names = list(names)
        self.weight = min(3, jobs) if "crash" in names else 1
        self.estimate = sum(TESTS[n] / (self.weight if n == "crash" else 1) for n in names)
        self.proc = None

    def start_next(self):
        name = self.names.pop(0)
        folder = os.path.join(OUT, name)
        shutil.rmtree(folder, ignore_errors=True)
        os.makedirs(folder)
        env = dict(os.environ, LEANOS_TEST_DIR=folder)
        if name == "crash":
            env["CRASH_LANES"] = str(self.weight)
        self.name, self.log = name, open(os.path.join(folder, "output.txt"), "wb")
        self.t0 = time.monotonic()
        # a session of its own: QEMU and any servers the test starts go down with it
        self.proc = subprocess.Popen([os.path.join(ROOT, "test", name + ".sh")], cwd=ROOT, env=env,
                                     stdin=subprocess.DEVNULL, stdout=self.log,
                                     stderr=subprocess.STDOUT, start_new_session=True)


def main():
    jobs = int(os.environ.get("JOBS") or default_jobs())
    if jobs < 1:
        sys.exit("JOBS must be at least 1")
    wanted = sys.argv[1:] or list(TESTS)
    unknown = [n for n in wanted if n not in TESTS]
    if unknown:
        sys.exit(f"no such test: {', '.join(unknown)} (the tests: {', '.join(TESTS)})")
    units, chained = [], set()
    for chain in CHAINS:
        names = [n for n in chain if n in wanted]
        if names:
            units.append(Unit(names, jobs))
            chained.update(names)
    units += [Unit([n], jobs) for n in wanted if n not in chained]
    units.sort(key=lambda u: -u.estimate)
    os.makedirs(OUT, exist_ok=True)
    print(f"test/all.py: {len(wanted)} tests, up to {jobs} at once (JOBS); each one's output when it ends",
          flush=True)

    def stop(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop)      # a make that is stopped stops the tests too
    t0 = time.monotonic()
    pending, running, results = units, [], {}
    try:
        while pending or running:
            free = jobs - sum(u.weight for u in running)
            for u in list(pending):
                if u.weight <= free:
                    pending.remove(u)
                    u.start_next()
                    running.append(u)
                    free -= u.weight
            time.sleep(0.2)
            for u in list(running):
                status = u.proc.poll()
                if status is None:
                    continue
                took = time.monotonic() - u.t0
                u.log.close()
                results[u.name] = (status, took)
                verdict = "ok" if status == 0 else f"FAILED (status {status})"
                print(f"\n==== {u.name}: {verdict}, {took:.0f} s", flush=True)
                with open(os.path.join(OUT, u.name, "output.txt"), errors="replace") as f:
                    sys.stdout.write(f.read())
                sys.stdout.flush()
                if u.names:
                    u.start_next()          # the next test in its chain
                else:
                    running.remove(u)
    except KeyboardInterrupt:
        # stop every running test and what it started (its servers clean up on the way out)
        for sig in (signal.SIGTERM, signal.SIGKILL):
            for u in running:
                try:
                    os.killpg(u.proc.pid, sig)
                except ProcessLookupError:
                    pass
            if sig == signal.SIGTERM:
                time.sleep(2)
        print("\ntest/all.py: interrupted", flush=True)
        return 130

    wall = time.monotonic() - t0
    print("\n==== summary")
    width = max(map(len, wanted))
    for name in wanted:
        status, took = results[name]
        print(f"  {name:<{width}} {'ok' if status == 0 else 'FAILED':<7} {took:5.0f} s")
    failed = [n for n in wanted if results[n][0] != 0]
    total = sum(took for _, took in results.values())
    print(f"{len(wanted) - len(failed)} of {len(wanted)} tests passed in {wall:.0f} s, "
          f"up to {jobs} at once ({total:.0f} s of tests)")
    if failed:
        print(f"FAIL: {', '.join(failed)} (output in build/test/NAME/output.txt)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
