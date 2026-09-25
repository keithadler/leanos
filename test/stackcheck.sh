#!/bin/bash
# The kernel stack's worst case, argued from the code rather than measured (test/stack.sh
# measures it): tools/stackcheck.py takes each function's frame from clang (-fstack-usage, in
# an analysis build whose code must match the image's) and the calls from the image itself,
# bounds each recursion it finds by its table (the task list, reply slots, pending lines), and
# fails on recursion or an indirect call it cannot bound, or a worst case over half the stack.
# Its self-test first checks that it does fail on such cases.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
out=$(make -s -j4 stackcheck 2>&1)
status=$?
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the stack check failed (status $status)"
echo "$out" | grep -q "^stackcheck: self-test ok" || fail "the self-test did not run"
bound=$(echo "$out" | sed -n "s/^ok: the kernel stack's worst case is \([0-9]*\) bytes.*/\1/p")
[ -n "$bound" ] || fail "no worst case reported"
echo "ok: the kernel stack needs at most $bound bytes of its 65536"
