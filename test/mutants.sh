#!/bin/bash
# Breaks the kernel on purpose, one way at a time, and checks the proofs reject each
# break. A mutant that still builds means a guarantee is weaker than it claims.
set -u
cd "$(dirname "$0")/.."
backup=$(mktemp)
cp LeanOS/Kernel.lean "$backup"
trap 'cp "$backup" LeanOS/Kernel.lean; rm -f "$backup"' EXIT

survived=0
mutant() {
  local name=$1 from=$2 to=$3
  cp "$backup" LeanOS/Kernel.lean
  python3 - "$from" "$to" <<'PY'
import sys
p = 'LeanOS/Kernel.lean'
s = open(p).read()
if sys.argv[1] not in s:
    sys.exit('mutation target not found: ' + sys.argv[1])
open(p, 'w').write(s.replace(sys.argv[1], sys.argv[2], 1))
PY
  if lake build >/dev/null 2>&1; then
    echo "SURVIVED: $name"; survived=1
  else
    echo "caught: $name"
  fi
}

mutant "derive grants whatever is asked" \
  "⟨c.frame, c.rights.meet (Rights.ofBits bits)⟩" "⟨c.frame, Rights.ofBits bits⟩"
mutant "map ignores the capability's frame" \
  "⟨vpn, c.frame, c.rights⟩ :: dropVpn" "⟨vpn, c.frame + 1, c.rights⟩ :: dropVpn"
mutant "map outside the user window" \
  "if vpn < userPages && c.rights.r then" "if c.rights.r then"
mutant "write skips the page check" \
  "allReadable t.maps ((va - userBase) / pageSize)" "true || allReadable t.maps ((va - userBase) / pageSize)"
mutant "user pages always executable" \
  "privNoExec + (if m.rights.x then 0 else userNoExec)" "privNoExec + 0"
mutant "read-only pages writable" \
  "(if m.rights.w then apUserRW else apUserRO)" "apUserRW"
mutant "kernel RAM executable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + shInner + accessFlag"
mutant "kernel RAM readable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + apUserRO + shInner + accessFlag + userNoExec"
mutant "scheduler may pick a stopped task" \
  "if isAlive ts j then some j else findAlive ts (j + 1) fuel" "some j"

cp "$backup" LeanOS/Kernel.lean
lake build >/dev/null 2>&1 || { echo "FAIL: the unmutated kernel no longer builds"; exit 1; }
[ $survived -eq 0 ] && echo "ok: every mutant was caught by the proofs" || exit 1
