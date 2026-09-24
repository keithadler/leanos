#!/bin/bash
# web, the text browser on the card, and the network by consent. Started with `run web`, the
# USB driver refuses it: Terminal did not allow it. Started with `run -net web`, it loads a
# page from a web server on the host (title, heading, two links, a script it never shows)
# and follows a link by its number.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
www=$(mktemp -d)
cat > "$www/index.html" <<'HTML'
<!doctype html><html><head><title>leanos test</title><style>p { color: red }</style></head>
<body><h1>Hello &amp; welcome</h1><p>First the <a href="page2.html">second page</a>, then
<a href="/nowhere">nowhere</a>.</p><script>document.write("never shown")</script>
<ul><li>one</li><li>two</li></ul></body></html>
HTML
printf '<h1>Two</h1><p>You followed the link.</p>\n' > "$www/page2.html"
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
url = f"10.0.2.2:{os.environ['PORT']}/index.html\r"
steps = [wait_for("usb: network: address"), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run web\r"), wait_for("web: opened"), *keys(url), wait_for("web: http"),
         *click(194, 163), wait_for("web: window closed"),       # its close button
         *click(150, 300), *keys("run -net web\r"), wait_for("web: opened", 2),
         *keys(url), wait_for("web: http", 2), *keys("1\r"), wait_for("web: http", 3),
         *click(194, 163), wait_for("web: window closed", 2),     # and from the dock, as Apps starts it
         *click(*DOCK["Web"]), wait_for("web: opened", 3), *keys(url.replace(".html", ".html?dock"))]
sys.exit(boot(200, net=True, steps=steps, until=f"web: http://10.0.2.2:{os.environ['PORT']}/index.html?dock", settle=1))
PY
)
status=$?
echo "$out" | grep -E "^(web|terminal: run|usb: network: slot)" | sed "s/:$port/:PORT/; s/^/  | /"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "web: http://10.0.2.2:$port/index.html -> not allowed to use the network: start it with run -net web" \
  || fail "web reached the network without being allowed"
echo "$out" | grep -qx "usb: network: slot 10 may use the network" || fail "run -net did not allow it"
echo "$out" | grep -qE "^web: http://10.0.2.2:$port/index.html -> [0-9]+ bytes, HTTP 200, 2 links, [0-9]+ lines: leanos test$" \
  || fail "the page did not load with its title and two links"
echo "$out" | grep -qE "^web: http://10.0.2.2:$port/page2.html -> [0-9]+ bytes, HTTP 200, 0 links" || fail "link 1 did not lead to page 2"
echo "$out" | grep -qE "^web: http://10.0.2.2:$port/index.html\?dock -> [0-9]+ bytes, HTTP 200" || fail "web from the dock did not load the page"
echo "ok: web is refused the network until Terminal allows it, then loads a page and follows a link; from the dock it may"
