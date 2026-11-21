#!/bin/bash
# The network service against a client and a server that mean it harm. The service is the
# USB driver, which is also the USB keyboard and mouse: if it stops, or waits for good, so
# do they, and so does every program Terminal or Apps starts next (each start asks it who
# may use the network).
#
#   1. A hostile client. netrace (user/progs/netrace.c), allowed the network, sends 200
#      requests as plain sends and keeps changing the buffer it lent while the service
#      reads it. The service used to read a name in that buffer until a 0 it had written
#      once, and ran off the buffer's end: the USB driver stopped. It must still answer
#      netrace's last call, and Terminal's ping after it.
#   2. A hostile server. A web server on the host answers with a header and then one byte
#      every two seconds, for ever. Terminal's `get` used to wait as long as the server
#      liked (ten seconds after each byte), and nothing else was answered meanwhile. It
#      must give up within NET_REQUEST_MS (30 s) and say so.
#   3. The same server, asked by `web` in an open slot, and web killed while it waits. The
#      service must drop the request at once, so the next `run` (which asks the service)
#      starts its program right away, and a ping is answered.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/netrace.elf || fail "netrace did not build"
card=$T/sd-netsafe.img
python3 tools/mksd.py "$card" netrace=build/progs/netrace.elf web=build/progs/web.elf hello=build/progs/hello.elf >/dev/null \
  || fail "no card"

port=$((20000 + RANDOM % 20000))
python3 - $port <<'SLOW' &
import socket, sys, threading, time
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", int(sys.argv[1])))
s.listen(8)
def trickle(c):
    try:
        c.recv(4096)
        c.sendall(b"HTTP/1.0 200 OK\r\nContent-Type: text/html\r\n\r\n<h1>Slow</h1>")
        while True:
            time.sleep(2)
            c.sendall(b".")
    except OSError:
        pass
while True:
    c, _ = s.accept()
    threading.Thread(target=trickle, args=(c,), daemon=True).start()
SLOW
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
sleep 1

out=$(PORT=$port python3 - "$card" <<'PY'
import os, sys, time
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
front = click(*DOCK["Terminal"])
url = f"http://10.0.2.2:{os.environ['PORT']}/slow"

# Host times of the lines the checks below compare, printed as "netsafe: NAME at N s".
# "sent" is the Return that ends Terminal's `get`: its third (run, ping, get).
t0 = time.monotonic()
returns, marked = [0], set()
MARKS = (("gave up", "usb: network: gave up a page for Terminal"), ("kill", "terminal: kill 10"), ("hello", "hello: opened"))
def mark(name):
    if name not in marked:
        marked.add(name)
        print(f"netsafe: {name} at {time.monotonic() - t0:.1f} s", flush=True)
def on_line(line):
    print(line, flush=True)
    if line.startswith("display: key return to Terminal"):
        returns[0] += 1
        if returns[0] == 3: mark("sent")
    for name, prefix in MARKS:
        if line.startswith(prefix): mark(name)

steps = [wait_for("usb: network: address"), *front, wait_for("terminal: opened"),
         # 1. the hostile client
         *keys("run -net netrace\r"), wait_for("netrace: after them"), *front,
         *keys("ping 10.0.2.2\r"), wait_for("terminal: ping"),
         # 2. the hostile server, asked by Terminal
         *keys(f"get {url}\r"), wait_for("terminal: get"),
         # 3. asked by web, which is then killed while it waits
         *keys("run -net web\r"), wait_for("web: opened"), *keys(url.replace("http://", "") + "\r"), pause(3),
         *front, *keys("kill 10\r"), wait_for("terminal: kill 10"),
         *keys("run hello\r"), wait_for("hello: opened"), *front,
         *keys("ping 10.0.2.2\r"), wait_for("terminal: ping", 2), pause(1),
         *click(40, 15), *click(60, 80), wait_for("leanos: switched off")]
sys.exit(boot(150, net=True, sd=sys.argv[1], steps=steps, on_line=on_line, clock_from="usb: network: address"))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(netrace|netsafe|usb: network: (gave|slot)|terminal: (run|get|ping|kill)|web: |hello: opened|leanos: [a-z]+ stopped)" \
  | sed "s/:$port/:PORT/g; s/^/  | /"
[ $status -eq 0 ] || fail "the run did not finish (status $status): the network service waits for good, or stopped?"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: [a-z]+ stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or app stopped: $bad"

# 1.
echo "$out" | grep -qx "netrace: 200 plain sends, the buffer changed under each" || fail "netrace did not send its 200 requests"
echo "$out" | grep -qx "netrace: after them the network service answers a call with 0" \
  || fail "the network service did not answer netrace after its plain sends"
[ "$(echo "$out" | grep -cx "terminal: ping 10.0.2.2 -> 4 of 4 answered")" = 2 ] || fail "a ping was not answered: $(echo "$out" | grep "^terminal: ping")"

# 2.
echo "$out" | grep -qx "usb: network: gave up a page for Terminal: it took too long" || fail "the service did not give up the slow page"
t=$(echo "$out" | awk '/^netsafe: sent at/ {s = $4} /^netsafe: gave up at/ {print int($5 - s + 0.5); exit}')
[ -n "$t" ] && [ "$t" -ge 25 ] && [ "$t" -le 40 ] || fail "the slow page was given up after ${t:-?} s, not about 30"

# 3.
echo "$out" | grep -qx "usb: network: gave up a page for slot 10: its program is gone" || fail "the service kept waiting for a program that was killed"
k=$(echo "$out" | awk '/^netsafe: kill at/ {s = $4} /^netsafe: hello at/ {print int($4 - s + 0.5); exit}')
[ -n "$k" ] && [ "$k" -le 8 ] || fail "after the kill the next program took ${k:-?} s to start: the service was still waiting"
echo "ok: 200 plain sends with the buffer changing under each, and the service still answers; a page sent a byte every 2 s is given up after $t s; a killed program's request is dropped, and the next program starts $k s after the kill"
