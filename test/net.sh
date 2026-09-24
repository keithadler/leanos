#!/bin/bash
# The network: a USB network adapter on QEMU's user network (the host is 10.0.2.2). The USB
# driver gets an address by DHCP; Terminal shows it (ip), pings the host (ping), and fetches
# two files from a web server on the host over TCP (get): a small one, read back with cat, and
# 300 KiB of one letter, checked whole with verify.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
www=$(mktemp -d)
printf 'Hello from the host, fetched over TCP by leanos.\n' > "$www/hello.txt"
python3 -c "import sys; sys.stdout.write('z' * 307200)" > "$www/big.txt"
port=$((20000 + RANDOM % 20000))
(cd "$www" && exec python3 -m http.server $port --bind 127.0.0.1 >/dev/null 2>&1) &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null; rm -rf "$www"' EXIT
sleep 1

out=$(PORT=$port python3 - <<'PY'
import os, sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
port = os.environ["PORT"]
steps = [wait_for("usb: network"), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("ip\r"), wait_for("terminal: ip"),
         *keys("ping 10.0.2.2\r"), wait_for("terminal: ping"),
         *keys(f"get http://10.0.2.2:{port}/hello.txt\r"), wait_for("terminal: get"),
         *keys("cat hello.txt\r"), wait_for("terminal: cat"),
         *keys(f"get http://10.0.2.2:{port}/big.txt\r"), wait_for("terminal: get", 2),
         *keys("verify big.txt\r"), wait_for("terminal: verify")]
sys.exit(boot(240, net=True, steps=steps, until="terminal: verify", settle=0.5))
PY
)
status=$?
echo "$out" | grep -E "^(usb: (device .*network|network)|terminal: (ip|ping|get|cat|verify))" | sed "s/:$port/:PORT/; s/^/  | /"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "usb: network: address 10.0.2.15, gateway 10.0.2.2, DNS 10.0.2.3" || fail "no address from DHCP"
echo "$out" | grep -qx "terminal: ip -> 10.0.2.15" || fail "ip did not show the address"
echo "$out" | grep -qx "terminal: ping 10.0.2.2 -> 4 of 4 answered" || fail "the host did not answer pings"
echo "$out" | grep -qx "terminal: get http://10.0.2.2:$port/hello.txt -> 49 bytes, HTTP 200" || fail "the small file did not come"
echo "$out" | grep -qx "terminal: cat hello.txt -> 49 bytes" || fail "the small file was not saved"
echo "$out" | grep -qx "terminal: verify big.txt -> 307200 bytes of 'z'" || fail "300 KiB did not arrive whole"
echo "ok: DHCP, ping, and 300 KiB over TCP from a web server, through the USB network adapter"
