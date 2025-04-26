#!/usr/bin/env sh
lake build &&
lake lean scripts/PrintInfo.lean &&
python3 scripts/printinfo.py &&
cp scripts/content.tex blueprint/src/content.tex
