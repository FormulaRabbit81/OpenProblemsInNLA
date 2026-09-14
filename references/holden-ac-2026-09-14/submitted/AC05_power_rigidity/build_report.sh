#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$work" \
       "$root/report/AC05_power_rigidity.tex" > "$work/pass-$pass.log"
done
cp "$work/AC05_power_rigidity.pdf" "$root/report/AC05_power_rigidity.pdf"
cp "$work/pass-3.log" "$root/results/latex_build.log"
printf 'Built %s\n' "$root/report/AC05_power_rigidity.pdf"
