#!/bin/bash
# Verified boot, attacked: flip one bit of carol's code inside the kernel image, boot it,
# and check the kernel refuses carol (and only carol), and that the boot screen says so.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

python3 - <<'PY' || fail "could not tamper with the image"
image = open("build/kernel8.img", "rb").read()
carol = open("build/user/carol.bin", "rb").read()
at = image.find(carol)
assert at >= 0 and image.find(carol, at + 1) < 0, "carol's code is not in the image exactly once"
patched = bytearray(image)
patched[at + len(carol) // 2] ^= 0x01
open("build/kernel8-tampered.img", "wb").write(patched)
print(f"tampered: flipped one bit of carol's code at image offset {at + len(carol) // 2:#x}")
PY

out=$(python3 test/run.py 40 --image=build/kernel8-tampered.img)
status=$?
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the tampered image did not reach idle (status $status)"

echo "$out" | grep -qx "leanos: carol refused: what was loaded does not match the boot manifest" || fail "carol was not refused"
for who in alice display mallory input fs; do
  echo "$out" | grep -q "^leanos: $who verified, sha256 " || fail "$who was not verified"
done
echo "$out" | grep -q "^carol: " && fail "carol ran"
echo "$out" | grep -qx "display: boot checks shown: 5 verified, 1 refused" || fail "the boot screen did not show the refusal"
echo "$out" | grep -q "^mallory: I am task 2" || fail "the other tasks did not run"

python3 - <<'PY' || fail "the boot screen does not show carol refused"
data = open("build/logo.ppm", "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
at = lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
def count(k, pred):
    y0 = 462 + k * 16
    return sum(1 for y in range(y0, y0 + 14) for x in range(382, 396) if pred(*at(x, y)))
red = lambda r, g, b: r > 180 and g < 120 and b < 120
green = lambda r, g, b: g > 150 and r < 120
assert count(3, red) > 30 and count(3, green) == 0, ("carol's mark", count(3, red), count(3, green))
for k in (0, 1, 2, 4, 5):
    assert count(k, green) > 30 and count(k, red) == 0, ("mark", k, count(k, green), count(k, red))
print("ok: the boot screen shows carol refused and the others verified")
PY
echo "ok: a one-bit change to carol's code keeps carol from running"

# The same attack on an app that is not loaded at boot: Security is only loaded, and checked,
# when the dock starts it. It must be refused then, and nothing else may change.
python3 - <<'PY' || fail "could not tamper with the image"
image = open("build/kernel8.img", "rb").read()
app = open("build/user/security.bin", "rb").read()
at = image.find(app)
assert at >= 0 and image.find(app, at + 1) < 0, "Security's code is not in the image exactly once"
patched = bytearray(image)
patched[at + len(app) // 2] ^= 0x01
open("build/kernel8-tampered.img", "wb").write(patched)
print(f"tampered: flipped one bit of Security's code at image offset {at + len(app) // 2:#x}")
PY

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for
steps = [mouse("d", 648, 548), mouse("u", 648, 548), wait_for("display: Security was refused")]
sys.exit(boot(60, steps=steps, until="display: Security was refused", image="build/kernel8-tampered.img"))
PY
)
status=$?
echo "$out" | grep -E "^(leanos: security|display: (start|Security))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the tampered app was not refused (status $status)"
echo "$out" | grep -qx "leanos: security refused: what was loaded does not match the boot manifest" || fail "Security was not refused"
echo "$out" | grep -qx "display: boot checks shown: 6 verified, 0 refused" || fail "the boot checks changed"
echo "$out" | grep -q "^security: " && fail "the tampered Security ran"
echo "ok: a one-bit change to an app keeps it from running when it is started"
