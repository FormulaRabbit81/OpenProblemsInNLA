#!/usr/bin/env bash
set -euo pipefail
REPORT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required to build the report.' >&2; exit 1; }
BUILD_DIR="$(mktemp -d)"
trap 'rm -rf "$BUILD_DIR"' EXIT
cd "$REPORT_DIR"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD_DIR" AC01_round3_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD_DIR" AC01_round3_report.tex
cp "$BUILD_DIR/AC01_round3_report.pdf" "$REPORT_DIR/AC01_round3_report.pdf"
printf '\nBuilt %s\n' "$REPORT_DIR/AC01_round3_report.pdf"
