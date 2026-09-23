#!/usr/bin/env python3
"""Watch leanos boot from a browser.

Serves a console page on http://127.0.0.1:8796. Each press of "Boot" starts a real QEMU
run of build/kernel8.img on this machine and streams its serial console to the page, line
by line, as it happens. Nothing is emulated in the browser; it only shows the output.
"""
import http.server
import json
import os
import socketserver
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PORT = 8796
QEMU = ["qemu-system-aarch64", "-M", "raspi4b", "-nographic", "-semihosting",
        "-kernel", os.path.join(ROOT, "build", "kernel8.img")]

PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>leanos console</title>
<style>
:root { --bg:#f6f5f1; --panel:#ffffff; --ink:#1d1d1b; --dim:#6b6a64; --line:#dddbd3;
        --kernel:#2f5d8a; --alice:#2e7d4f; --bob:#9a5b13; --carol:#7a3f8f; --bad:#b3261e; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#141412; --panel:#1c1c1a; --ink:#e9e7e1; --dim:#9b998f; --line:#33322e;
          --kernel:#8ab4e0; --alice:#7fcf9d; --bob:#e0a95c; --carol:#c99ad8; --bad:#f28b82; }
}
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--ink);
       font: 15px/1.5 -apple-system, system-ui, sans-serif; }
main { max-width: 900px; margin: 0 auto; padding: 24px 16px 48px; }
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
.bob { color: var(--bob); } .carol { color: var(--carol); }
.bad { color: var(--bad); font-weight: 600; }
</style></head>
<body><main>
<h1>leanos console</h1>
<p class="sub">QEMU's Raspberry Pi 4 (<code>raspi4b</code>) running build/kernel8.img on this Mac,
streamed from its serial port. Times are since power-on.</p>
<div class="bar"><button id="boot">Boot</button><span id="status">Ready</span></div>
<pre id="out"></pre>
</main>
<script>
const out = document.getElementById('out'), btn = document.getElementById('boot'),
      status = document.getElementById('status');
function cls(line) {
  if (/PANIC|SHOULD NOT|CHANGED/.test(line)) return 'bad';
  const m = line.match(/^(\w+):/);
  if (!m) return '';
  return {leanos:'kernel', alice:'alice', bob:'bob', carol:'carol'}[m[1]] || '';
}
function boot() {
  out.textContent = ''; btn.disabled = true; status.textContent = 'Booting…';
  const es = new EventSource('/boot');
  es.onmessage = (e) => {
    const d = JSON.parse(e.data);
    if (d.done) {
      status.textContent = d.code === 0 ? 'Machine powered itself off' : 'QEMU exited with status ' + d.code;
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
        proc = subprocess.Popen(QEMU, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        try:
            for raw in proc.stdout:
                line = raw.decode(errors="replace").rstrip("\r\n")
                if line:
                    self.send_event({"t": time.monotonic() - start, "line": line})
            code = proc.wait(timeout=30)
            self.send_event({"done": True, "code": code})
        except (BrokenPipeError, ConnectionResetError):
            pass
        finally:
            if proc.poll() is None:
                proc.kill()


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


if __name__ == "__main__":
    if not os.path.exists(QEMU[-1]):
        raise SystemExit("build/leanos.elf is missing: run `make` first")
    print(f"leanos console on http://127.0.0.1:{PORT}", flush=True)
    Server(("127.0.0.1", PORT), Handler).serve_forever()
