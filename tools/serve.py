#!/usr/bin/env python3
"""Watch leanos boot from a browser.

Serves a console page on http://127.0.0.1:8796. Each press of "Boot" starts a real QEMU
run of build/kernel8.img on this machine, streams its serial console to the page line by
line, and shows the screen once the system settles. Nothing is emulated in the browser;
it only shows what QEMU produced.
"""
import base64
import http.server
import json
import os
import socketserver
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "test"))
import run  # noqa: E402  (test/run.py: boots QEMU and captures the screen)

PORT = 8796
IMAGE = os.path.join(ROOT, "build", "kernel8.img")
BOOT_LOCK = threading.Lock()

PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>leanos console</title>
<style>
:root { --bg:#f6f5f1; --panel:#ffffff; --ink:#1d1d1b; --dim:#6b6a64; --line:#dddbd3;
        --kernel:#2f5d8a; --alice:#2e7d4f; --server:#1f6f78; --display:#1f6f78; --mallory:#9a5b13; --carol:#7a3f8f; --bad:#b3261e; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#141412; --panel:#1c1c1a; --ink:#e9e7e1; --dim:#9b998f; --line:#33322e;
          --kernel:#8ab4e0; --alice:#7fcf9d; --server:#7fd3dc; --display:#7fd3dc; --mallory:#e0a95c; --carol:#c99ad8; --bad:#f28b82; }
}
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--ink);
       font: 15px/1.5 -apple-system, system-ui, sans-serif; }
main { max-width: 1400px; margin: 0 auto; padding: 24px 16px 48px; }
.panes { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 640px); gap: 16px; align-items: start; }
@media (max-width: 1000px) { .panes { grid-template-columns: minmax(0, 1fr); } }
.screen { background: var(--panel); border: 1px solid var(--line); border-radius: 8px; padding: 8px; }
.screen img { display: block; width: 100%; height: auto; image-rendering: pixelated; border-radius: 4px; }
.screen p { margin: 8px 4px 2px; color: var(--dim); font-size: 13px; }
h1 { font-size: 20px; margin: 0 0 4px; }
p.sub { margin: 0 0 16px; color: var(--dim); }
.bar { display:flex; gap:12px; align-items:center; margin-bottom:12px; flex-wrap:wrap; }
button { font: inherit; padding: 6px 16px; border-radius: 6px; border: 1px solid var(--line);
         background: var(--panel); color: var(--ink); cursor: pointer; }
button:disabled { opacity: .5; cursor: default; }
#status { color: var(--dim); }
pre { background: var(--panel); border: 1px solid var(--line); border-radius: 8px;
      padding: 14px 16px; margin: 0; min-height: 420px; overflow-x: auto;
      font: 13px/1.6 ui-monospace, SFMono-Regular, Menlo, monospace; white-space: pre-wrap; }
.t { color: var(--dim); user-select: none; }
.kernel { color: var(--kernel); } .alice { color: var(--alice); }
.server { color: var(--server); } .display { color: var(--display); } .mallory { color: var(--mallory); } .carol { color: var(--carol); }
.bad { color: var(--bad); font-weight: 600; }
</style></head>
<body><main>
<h1>leanos console</h1>
<p class="sub">QEMU's Raspberry Pi 4 (<code>raspi4b</code>) running build/kernel8.img on this Mac:
its serial port as it happens (times since power-on), and its screen once the system settles.</p>
<div class="bar"><button id="boot">Boot</button><span id="status">Ready</span></div>
<div class="panes">
<pre id="out"></pre>
<div class="screen"><img id="screen" alt="The Pi's screen, 640 by 480" hidden><p id="screencap">The screen appears when the system settles.</p></div>
</div>
</main>
<script>
const out = document.getElementById('out'), btn = document.getElementById('boot'),
      status = document.getElementById('status');
function cls(line) {
  if (/PANIC|SHOULD NOT|CHANGED/.test(line)) return 'bad';
  const m = line.match(/^(\w+):/);
  if (!m) return '';
  return {leanos:'kernel', alice:'alice', server:'server', display:'display', mallory:'mallory', carol:'carol'}[m[1]] || '';
}
const screen = document.getElementById('screen'), screencap = document.getElementById('screencap');
function boot() {
  out.textContent = ''; btn.disabled = true; status.textContent = 'Booting…';
  screen.hidden = true; screencap.textContent = 'The screen appears when the system settles.';
  const es = new EventSource('/boot');
  es.onmessage = (e) => {
    const d = JSON.parse(e.data);
    if (d.screen) {
      screen.src = 'data:image/png;base64,' + d.screen; screen.hidden = false;
      screencap.textContent = 'Captured from QEMU when the kernel went idle.';
      return;
    }
    if (d.done) {
      status.textContent = d.code === 0 ? 'Done' : 'QEMU ended with status ' + d.code;
      btn.disabled = false; es.close(); return;
    }
    const row = document.createElement('div');
    const t = document.createElement('span'); t.className = 't';
    t.textContent = (d.t * 1000).toFixed(0).padStart(5) + ' ms  ';
    const s = document.createElement('span'); s.className = cls(d.line); s.textContent = d.line;
    row.append(t, s); out.append(row);
  };
  es.onerror = () => { status.textContent = 'Connection lost'; btn.disabled = false; es.close(); };
}
btn.onclick = boot;
boot();
</script></body></html>
"""


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def do_GET(self):
        if self.path == "/":
            body = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif self.path == "/boot":
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.stream_boot()
        else:
            self.send_error(404)

    def send_event(self, obj):
        self.wfile.write(b"data: " + json.dumps(obj).encode() + b"\n\n")
        self.wfile.flush()

    def stream_boot(self):
        start = time.monotonic()

        def line(text):
            self.send_event({"t": time.monotonic() - start, "line": text})

        def screen(png):
            self.send_event({"screen": base64.b64encode(open(png, "rb").read()).decode()})

        with BOOT_LOCK:  # one QEMU at a time: they share build/screen.*
            try:
                code = run.boot(30, on_line=line, on_screen=screen)
                self.send_event({"done": True, "code": code})
            except (BrokenPipeError, ConnectionResetError):
                pass


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


if __name__ == "__main__":
    if not os.path.exists(IMAGE):
        raise SystemExit("build/leanos.elf is missing: run `make` first")
    print(f"leanos console on http://127.0.0.1:{PORT}", flush=True)
    Server(("127.0.0.1", PORT), Handler).serve_forever()
