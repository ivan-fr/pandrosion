#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
if command -v tectonic >/dev/null; then
  tectonic --keep-logs --outdir build main.tex
elif command -v latexmk >/dev/null; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
else
  echo 'Install Tectonic or latexmk.' >&2
  exit 1
fi
cp build/main.pdf Reciprocal_Root_Geometry_v21.pdf
