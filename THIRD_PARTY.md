# Third-party assets

leanos's code is MIT (see [LICENSE](LICENSE)). These assets are built into the system image
by `tools/mkassets.py` and keep their own licenses. Nothing GPL-licensed goes into the image.

| Asset | Files | Source | License |
|---|---|---|---|
| Inter 4.1 (Regular, Medium, SemiBold, Bold) | `assets/fonts/*.ttf` | [rsms/inter](https://github.com/rsms/inter) release 4.1 | SIL Open Font License 1.1, [`assets/fonts/OFL.txt`](assets/fonts/OFL.txt) |
| JetBrains Mono 2.304 (Regular), Terminal's font | `assets/fonts/JetBrainsMono-Regular.ttf` | [JetBrains/JetBrainsMono](https://github.com/JetBrains/JetBrainsMono) tag v2.304 | SIL Open Font License 1.1, [`assets/fonts/JetBrainsMono-OFL.txt`](assets/fonts/JetBrainsMono-OFL.txt) |
| Fluent Emoji 3D: Memo, File folder, Laptop, Gear, Locked, Rocket, Alarm clock, Abacus, Shield, Globe with meridians, Snake, Seedling, Game die, Waving hand, Lady beetle, Pencil | `assets/icons/*.png` | [microsoft/fluentui-emoji](https://github.com/microsoft/fluentui-emoji) | MIT, [`assets/icons/LICENSE`](assets/icons/LICENSE) |

The fonts are rasterized and the icons scaled at build time by `tools/mkassets.py` and
`tools/mkicon.py`, which have their own TrueType reader and PNG decoder; the build downloads
nothing.

Not in this repository: the Raspberry Pi boot firmware (`start4.elf`, `fixup4.dat` and the
device-tree blob), which is the Raspberry Pi Foundation's and is fetched by
`tools/fetch-firmware.sh` only when you build an SD card image for a real Pi.

The leanos logo, the desktop's background pattern (computed by the display server) and the
5×7 fallback font (`user/font5x7.txt`) were made for this project.
