#!/bin/bash
# Downloads the two Raspberry Pi 4 boot firmware files leanos's card image needs into
# build/firmware/: start4.elf (the GPU's boot program) and fixup4.dat (its memory split).
# They are the Raspberry Pi Foundation's, under their own license (build/firmware/LICENCE.broadcom),
# from https://github.com/raspberrypi/firmware; leanos does not redistribute them.
set -eu
cd "$(dirname "$0")/.."
TAG=${1:-1.20250430}
BASE="https://github.com/raspberrypi/firmware/raw/$TAG/boot"
mkdir -p build/firmware
for f in start4.elf fixup4.dat LICENCE.broadcom; do
  echo "downloading $f ($TAG)"
  curl -fsSL -o "build/firmware/$f" "$BASE/$f"
done
echo "done: now run make pi-image"
