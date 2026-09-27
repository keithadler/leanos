#!/bin/bash
# The USB-A ports, without a Pi: the USB driver's xHCI code (user/xhci.c) and the machine
# layer's (arch/xhci.c) compiled for this machine and run against a model of an xHCI controller
# and the devices behind it, with the Lean kernel's own `sysXhci` deciding every system call the
# driver makes (test/xhci-sim/: sim.c says what is modelled and what is not).
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build/test/xhci}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

# The host's compiler: Xcode's on macOS (through xcrun, which gives it the SDK), else the system's.
if command -v xcrun >/dev/null; then CC="xcrun clang"; else CC=$(command -v clang || command -v cc) || fail "no C compiler for the host"; fi
$CC -std=gnu11 -O1 -g -Wall -Wextra -Werror -Wno-unused-function -Wno-sign-compare -Wno-unused-parameter \
  -fsanitize=undefined -fno-sanitize-recover=all \
  -o "$T/xhci-sim" test/xhci-sim/sim.c arch/xhci.c || fail "the simulator did not compile"
"$T/xhci-sim" lake env lean --run test/xhci-sim/Oracle.lean
