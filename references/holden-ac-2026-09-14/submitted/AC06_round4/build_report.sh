#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT
pdflatex -halt-on-error -interaction=nonstopmode -output-directory="$build_dir" report.tex > /dev/null
pdflatex -halt-on-error -interaction=nonstopmode -output-directory="$build_dir" report.tex > /dev/null
cp "$build_dir/report.pdf" report.pdf
cp "$build_dir/report.log" evidence/latex.log
printf 'Built %s/report.pdf\n' "$PWD"
