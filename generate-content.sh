#!/usr/bin/env sh
lake build &&
lake exe PrintInfo &&
python3 scripts/printinfo.py &&
cp scripts/content.tex blueprint/src/content.tex
