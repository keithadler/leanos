#!/usr/bin/env python3
"""Run leanos in a browser.

Serves a page on http://127.0.0.1:8796. "Boot" starts QEMU's Raspberry Pi 4 on this
machine with no window of its own (`-display none`); its screen is published over VNC on a
localhost-only WebSocket and drawn live in the page by noVNC, while the serial console
streams alongside. Keys and mouse on the screen are sent into the Pi's serial line, where
leanos's input driver reads them (the emulated Pi 4 has no USB). QEMU keeps running until
"Stop", the next "Boot", or the page going away.
"""
import http.server
import json
import os
import secrets
import socketserver
import subprocess
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PORT = 8796
VNC_DISPLAY = 1           # TCP 5901, localhost only
WS_PORT = 5701            # the WebSocket noVNC connects to
IMAGE = os.path.join(ROOT, "build", "kernel8.img")
SD_IMAGE = os.path.join(ROOT, "build", "sd.img")   # the Pi's SD card; kept, so files survive
SCREEN_W, SCREEN_H = 1024, 600   # fbWidth and fbHeight in LeanOS/Kernel.lean
QEMU = ["qemu-system-aarch64", "-M", "raspi4b", "-display", "none",
        "-vnc", f"127.0.0.1:{VNC_DISPLAY},websocket=127.0.0.1:{WS_PORT}",
        "-serial", "stdio", "-semihosting", "-kernel", IMAGE,
        "-drive", f"if=sd,format=raw,file={SD_IMAGE}"]

lock = threading.Lock()
current = {"proc": None, "id": ""}


def log(*parts):
    print(time.strftime("%H:%M:%S"), *parts, flush=True)


def stop_qemu(why):
    proc = current["proc"]
    if proc and proc.poll() is None:
        log("stopping QEMU:", why)
    current["proc"] = None
    if proc and proc.poll() is None:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()


PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>leanos</title>
<style>
:root { --bg:#f6f5f1; --panel:#ffffff; --ink:#1d1d1b; --dim:#6b6a64; --line:#dddbd3;
        --kernel:#2f5d8a; --alice:#2e7d4f; --display:#1f6f78; --mallory:#9a5b13; --carol:#7a3f8f; --bad:#b3261e; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#141412; --panel:#1c1c1a; --ink:#e9e7e1; --dim:#9b998f; --line:#33322e;
          --kernel:#8ab4e0; --alice:#7fcf9d; --display:#7fd3dc; --mallory:#e0a95c; --carol:#c99ad8; --bad:#f28b82; }
}
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--ink); font: 15px/1.5 -apple-system, system-ui, sans-serif; }
main { max-width: 1400px; margin: 0 auto; padding: 20px 16px 40px; }
h1 { font-size: 20px; margin: 0 0 4px; }
p.sub { margin: 0 0 14px; color: var(--dim); }
.bar { display:flex; gap:10px; align-items:center; margin-bottom:12px; flex-wrap:wrap; }
button { font: inherit; padding: 6px 16px; border-radius: 6px; border: 1px solid var(--line);
         background: var(--panel); color: var(--ink); cursor: pointer; }
button:disabled { opacity: .5; cursor: default; }
#status { color: var(--dim); }
.panes { display: grid; grid-template-columns: minmax(0, 1fr); gap: 16px; align-items: start; }
.screen { background: #000; border: 1px solid var(--line); border-radius: 8px; overflow: hidden;
          aspect-ratio: %SCREEN_W% / %SCREEN_H%; position: relative; max-width: %SCREEN_W%px; }
#vnc { position: absolute; inset: 0; }
#input { position: absolute; inset: 0; width: 100%; height: 100%; margin: 0; padding: 0; border: 0;
         resize: none; outline: none; cursor: none; opacity: 0; caret-color: transparent; }
.screen .off { position: absolute; inset: 0; display: grid; place-items: center; color: #9b998f; font-size: 14px; }
.screen .off[hidden] { display: none; }
pre { background: var(--panel); border: 1px solid var(--line); border-radius: 8px; padding: 12px 14px; margin: 0;
      height: 280px; overflow: auto; font: 12.5px/1.55 ui-monospace, SFMono-Regular, Menlo, monospace; white-space: pre-wrap; }
.t { color: var(--dim); user-select: none; }
.kernel { color: var(--kernel); } .alice { color: var(--alice); } .display { color: var(--display); }
.mallory { color: var(--mallory); } .carol { color: var(--carol); } .bad { color: var(--bad); font-weight: 600; }
</style></head>
<body><main>
<h1>leanos</h1>
<p class="sub">QEMU's Raspberry Pi 4 running build/kernel8.img on this Mac, with no window of its own.
The screen is live: click it, then type or drag windows. The serial console streams alongside.</p>
<div class="bar"><button id="boot">Boot</button><button id="stop" disabled>Stop</button><span id="status">Ready</span></div>
<div class="panes">
  <div class="screen"><div id="vnc"></div><textarea id="input" aria-label="The Pi's screen: click it to type" autocomplete="off" autocorrect="off" autocapitalize="off" spellcheck="false"></textarea><div class="off" id="off">Not running</div></div>
  <pre id="out"></pre>
</div>
</main>
<script type="module">
import RFB from 'https://cdn.jsdelivr.net/npm/@novnc/novnc@1.7.0/core/rfb.js';
const out = document.getElementById('out'), status = document.getElementById('status');
const bootBtn = document.getElementById('boot'), stopBtn = document.getElementById('stop');
const off = document.getElementById('off'), vncEl = document.getElementById('vnc');
let es = null, rfb = null, bootId = '';

function cls(line) {
  if (/PANIC|SHOULD NOT|CHANGED/.test(line)) return 'bad';
  const m = line.match(/^(\w+):/);
  return m ? ({leanos:'kernel', alice:'alice', display:'display', mallory:'mallory', carol:'carol'}[m[1]] || '') : '';
}
function connectScreen(tries) {
  if (rfb) { try { rfb.disconnect(); } catch (e) {} rfb = null; }
  const r = new RFB(vncEl, 'ws://127.0.0.1:%WS_PORT%');
  r.scaleViewport = true;
  r.viewOnly = true;       /* input goes over the serial line instead: see below */
  r.addEventListener('connect', () => { off.hidden = true; });
  r.addEventListener('disconnect', () => {
    if (rfb !== r) return;
    rfb = null;
    if (es && tries > 0) setTimeout(() => connectScreen(tries - 1), 300); else off.hidden = false;
  });
  rfb = r;
}
function finish(text) {
  if (es) { es.close(); es = null; }
  if (rfb) { const r = rfb; rfb = null; try { r.disconnect(); } catch (e) {} }
  off.hidden = false; off.textContent = 'Not running';
  bootBtn.disabled = false; stopBtn.disabled = true; status.textContent = text;
}
function boot() {
  if (es) es.close();
  out.textContent = ''; bootBtn.disabled = true; stopBtn.disabled = false;
  status.textContent = 'Booting…'; off.hidden = false; off.textContent = 'Starting…';
  es = new EventSource('/boot');
  es.onmessage = (e) => {
    const d = JSON.parse(e.data);
    if (d.started) { bootId = d.id; status.textContent = 'Running'; setTimeout(() => connectScreen(20), 200); return; }
    if (d.done) { finish(d.code === 0 ? 'The machine powered itself off' : 'Stopped'); return; }
    const row = document.createElement('div');
    const t = document.createElement('span'); t.className = 't';
    t.textContent = (d.t * 1000).toFixed(0).padStart(5) + ' ms  ';
    const s = document.createElement('span'); s.className = cls(d.line); s.textContent = d.line;
    row.append(t, s); out.append(row); out.scrollTop = out.scrollHeight;
    if (d.line.startsWith('leanos: idle')) status.textContent = 'Running, idle';
  };
  es.onerror = () => finish('Stopped');
}
/* Keys and mouse on the screen become bytes on the Pi's serial line: plain bytes for keys,
   ESC 'm' kind xxx yyy for the mouse (see user/input.c). Sent in order, one request at a time. */
const inputEl = document.getElementById('input');
let sendQueue = Promise.resolve();
function sendBytes(str) {
  const id = bootId;
  sendQueue = sendQueue.then(() => fetch('/input?id=' + id, {method: 'POST', body: str}).catch(() => {}));
}
function pad3(n) { return String(Math.max(0, Math.min(999, n))).padStart(3, '0'); }
function mouse(kind, e) {
  const r = inputEl.getBoundingClientRect();
  const x = Math.round((e.clientX - r.left) * %SCREEN_W% / r.width), y = Math.round((e.clientY - r.top) * %SCREEN_H% / r.height);
  sendBytes('\x1bm' + kind + pad3(Math.min(%SCREEN_W% - 1, x)) + pad3(Math.min(%SCREEN_H% - 1, y)));
}
let lastMove = 0, pendingMove = null;
inputEl.addEventListener('mousedown', (e) => { inputEl.focus(); mouse('d', e); e.preventDefault(); });
inputEl.addEventListener('mouseup', (e) => mouse('u', e));
inputEl.addEventListener('mousemove', (e) => {
  const now = performance.now();
  if (now - lastMove >= 30) { lastMove = now; mouse('v', e); }
  else { clearTimeout(pendingMove); pendingMove = setTimeout(() => { lastMove = performance.now(); mouse('v', e); }, 30); }
});
/* Text arrives through the field's input events, so typing, pasting and input methods all
   work; Enter and Backspace come from the key events. A line break inside text (pasted
   lines) is a Return too. */
inputEl.addEventListener('keydown', (e) => {
  const arrows = {ArrowUp: 'A', ArrowDown: 'B', ArrowRight: 'C', ArrowLeft: 'D'};
  if (arrows[e.key]) { sendBytes('\x1b[' + arrows[e.key]); e.preventDefault(); }
  else if (e.key === 'Enter') { sendBytes('\r'); e.preventDefault(); }
  else if (e.key === 'Backspace') { sendBytes('\x7f'); e.preventDefault(); }
});
inputEl.addEventListener('input', () => {
  const text = [...inputEl.value].map(c => c === '\n' ? '\r' : c)
    .filter(c => c === '\r' || (c >= ' ' && c.charCodeAt(0) < 127)).join('');
  inputEl.value = '';
  if (text) sendBytes(text);
});
bootBtn.onclick = boot;
stopBtn.onclick = () => { fetch('/stop?id=' + bootId, {method: 'POST'}); finish('Stopped'); };
/* A stop from a page that is going away names its own boot, so it can never stop a newer one. */
window.addEventListener('pagehide', () => { if (bootId) navigator.sendBeacon('/stop?id=' + bootId); });
boot();
</script></body></html>
""".replace("%WS_PORT%", str(WS_PORT)).replace("%SCREEN_W%", str(SCREEN_W)).replace("%SCREEN_H%", str(SCREEN_H))


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

    def boot_id(self):
        """The boot a request names. Boot ids are random, so a page left over from an
        earlier server can never name the current boot."""
        query = self.path.partition("?")[2]
        for part in query.split("&"):
            key, _, value = part.partition("=")
            if key == "id" and value:
                return value
        return None

    def do_POST(self):
        path = self.path.partition("?")[0]
        if path == "/input":
            data = self.rfile.read(int(self.headers.get("Content-Length", 0) or 0))
            with lock:
                proc = current["proc"]
                if proc and proc.poll() is None and proc.stdin and self.boot_id() == current["id"]:
                    try:
                        proc.stdin.write(data)
                        proc.stdin.flush()
                    except OSError:
                        pass
            self.send_response(204)
            self.end_headers()
        elif path == "/stop":
            self.rfile.read(int(self.headers.get("Content-Length", 0) or 0))
            with lock:
                log("stop request for boot", self.boot_id(), "current", current["id"])
                if self.boot_id() == current["id"]:
                    stop_qemu("the page asked")
            self.send_response(204)
            self.end_headers()
        else:
            self.send_error(404)

    def send_event(self, obj):
        self.wfile.write(b"data: " + json.dumps(obj).encode() + b"\n\n")
        self.wfile.flush()

    def stream_boot(self):
        with lock:
            stop_qemu("a new boot")
            proc = subprocess.Popen(QEMU, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            current["proc"] = proc
            my_id = secrets.token_hex(8)
            current["id"] = my_id
        start = time.monotonic()
        try:
            self.send_event({"started": True, "id": my_id})
            for raw in proc.stdout:
                line = raw.decode(errors="replace").rstrip("\r\n")
                if line:
                    self.send_event({"t": time.monotonic() - start, "line": line})
            self.send_event({"done": True, "code": proc.wait()})
        except (BrokenPipeError, ConnectionResetError) as e:
            log("event stream closed:", repr(e))
        finally:
            with lock:
                if current["proc"] is proc:
                    stop_qemu("its page went away")
                elif proc.poll() is None:
                    proc.kill()


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


if __name__ == "__main__":
    if not os.path.exists(IMAGE):
        raise SystemExit("build/kernel8.img is missing: run `make` first")
    if not os.path.exists(SD_IMAGE):
        # the card `make` builds: welcome.txt and the programs Terminal can run
        import shutil
        shutil.copyfile(os.path.join(ROOT, "build", "sd-template.img"), SD_IMAGE)
    print(f"leanos in the browser on http://127.0.0.1:{PORT}", flush=True)
    try:
        Server(("127.0.0.1", PORT), Handler).serve_forever()
    finally:
        stop_qemu("?")
