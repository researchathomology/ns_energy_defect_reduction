#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode reduction.tex >/dev/null 2>&1 || true
grep -ciE "undefined" reduction.log | awk '{print "undefined refs/citations:", $1}'
grep -c "Overfull" reduction.log || true
pdfinfo reduction.pdf | grep Pages
