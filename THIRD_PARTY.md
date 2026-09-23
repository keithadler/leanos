# Third-party assets

leanos's code is MIT (see [LICENSE](LICENSE)). These assets are built into the system image
by `tools/mkassets.py` and keep their own licenses. Nothing GPL-licensed goes into the image.

| Asset | Files | Source | License |
|---|---|---|---|
| Inter 4.1 (Regular, Medium, SemiBold, Bold) | `assets/fonts/*.ttf` | [rsms/inter](https://github.com/rsms/inter) release 4.1 | SIL Open Font License 1.1, [`assets/fonts/OFL.txt`](assets/fonts/OFL.txt) |
| Fluent Emoji 3D: Memo, File folder, Laptop, Gear, Locked | `assets/icons/*.png` | [microsoft/fluentui-emoji](https://github.com/microsoft/fluentui-emoji) | MIT, [`assets/icons/LICENSE`](assets/icons/LICENSE) |
| "Earthrise", Apollo 8, 24 December 1968, photographed by William Anders | `assets/wallpapers/earthrise-512x300.png` | NASA, via [Wikimedia Commons](https://commons.wikimedia.org/wiki/File:NASA-Apollo8-Dec24-Earthrise.jpg) | Public domain (a work of NASA) |

The wallpaper was cropped to the screen's shape and scaled once with macOS `sips`:

```bash
sips -s format png -c 1406 2400 --cropOffset 617 0 NASA-Apollo8-Dec24-Earthrise.jpg --out crop.png
sips -z 300 512 crop.png --out assets/wallpapers/earthrise-512x300.png
```

The fonts are rasterized and the icons scaled at build time by `tools/mkassets.py`, which
has its own TrueType reader and PNG decoder; the build downloads nothing.

The leanos logo and the 5×7 fallback font (`user/font5x7.txt`) were drawn for this project.
