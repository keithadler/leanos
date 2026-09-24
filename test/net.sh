#!/bin/bash
# The network: a USB network adapter on QEMU's user network (the host is 10.0.2.2). The USB
# driver gets an address by DHCP; Terminal shows it (ip), pings the host (ping), and fetches
# two files from a web server on the host over TCP (get): a small one, read back with cat, and
# 300 KiB of one letter, checked whole with verify. Then the time of day: a time server on
# the host (NTP, over UDP) says it is 2026-01-02 03:04:05 UTC; ntp sets the kernel's time from
# it, and date reads it back, a moment later.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
www=$(mktemp -d)
printf 'Hello from the host, fetched over TCP by leanos.\n' > "$www/hello.txt"
python3 -c "import sys; sys.stdout.write('z' * 307200)" > "$www/big.txt"
port=$((20000 + RANDOM % 20000))
(cd "$www" && exec python3 -m http.server $port --bind 127.0.0.1 >/dev/null 2>&1) &
server=$!
ntp_port=$((20000 + RANDOM % 20000))
python3 - $ntp_port <<'NTP' &
import socket, struct, sys
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("127.0.0.1", int(sys.argv[1])))
when = 1767323045 + 2208988800           # 2026-01-02 03:04:05 UTC, in NTP's seconds since 1900
while True:
    q, a = s.recvfrom(512)
    if len(q) >= 48 and q[0] & 7 == 3:
        s.sendto(bytes([0x24, 2, 6, 0xec]) + bytes(20) + q[40:48] + struct.pack(">IIII", when, 0, when, 0), a)
NTP
ntp=$!
trap 'kill $server $ntp 2>/dev/null; wait $server $ntp 2>/dev/null; rm -rf "$www"' EXIT
sleep 1

out=$(PORT=$port NTP=$ntp_port python3 - <<'PY'
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
         *keys("verify big.txt\r"), wait_for("terminal: verify"),
         *keys(f"ntp 10.0.2.2:{os.environ['NTP']}\r"), wait_for("terminal: ntp"),
         *keys("date\r"), wait_for("terminal: date")]
sys.exit(boot(240, net=True, steps=steps, until="terminal: date", settle=0.5))
PY
)
status=$?
echo "$out" | grep -E "^(usb: (device .*network|network)|terminal: (ip|ping|get|cat|verify|ntp|date))" | sed "s/:$port/:PORT/; s/:$ntp_port/:NTP/; s/^/  | /"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "usb: network: address 10.0.2.15, gateway 10.0.2.2, DNS 10.0.2.3" || fail "no address from DHCP"
echo "$out" | grep -qx "terminal: ip -> 10.0.2.15" || fail "ip did not show the address"
echo "$out" | grep -qx "terminal: ping 10.0.2.2 -> 4 of 4 answered" || fail "the host did not answer pings"
echo "$out" | grep -qx "terminal: get http://10.0.2.2:$port/hello.txt -> 49 bytes, HTTP 200" || fail "the small file did not come"
echo "$out" | grep -qx "terminal: cat hello.txt -> 49 bytes" || fail "the small file was not saved"
echo "$out" | grep -qx "terminal: verify big.txt -> 307200 bytes of 'z'" || fail "300 KiB did not arrive whole"
echo "$out" | grep -qx "terminal: ntp 10.0.2.2:$ntp_port -> 2026-01-02 03:04:05 UTC" || fail "the time server's time was not set"
echo "$out" | grep -qE "^terminal: date -> 2026-01-02 03:04:(0[5-9]|[1-5][0-9]) UTC$" || fail "date did not read back the time"
echo "ok: DHCP, ping, 300 KiB over TCP from a web server, and the time of day from a time server, through the USB network adapter"
