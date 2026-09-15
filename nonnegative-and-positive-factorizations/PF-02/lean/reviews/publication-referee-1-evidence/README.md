# PF-02 independent publication referee 1 evidence

This evidence supplements the separately sealed mathematical-source and
authenticated Linux operational reviews. It records the exact publication
bytes, preservation of the original page and all other canonical pages,
unchanged proof/frozen inputs, catalog counts and independent PDF inspection.

The independent commands were:

```sh
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 -m unittest discover -s tests -p test_problem_ids.py -v
python tools/lean/validate_manifest.py nonnegative-and-positive-factorizations/PF-02/lean
pdfinfo nonnegative-and-positive-factorizations/PF-02/problem.pdf
pdftotext -layout nonnegative-and-positive-factorizations/PF-02/problem.pdf pdf-text.txt
pdftoppm -png -r 120 nonnegative-and-positive-factorizations/PF-02/problem.pdf page
git -c core.whitespace=-blank-at-eol diff --check
python3 audit-publication.py
```

The metadata validator used the existing audit Python environment containing
the repository's declared requirements. All commands passed. Both independently
rendered pages were actually viewed by the referee. The audit script retains
the original absolute scratch paths and requires the reviewed pre-commit
publication state; its JSON records all 299 passed checks and exact file hashes.

The exception for trailing spaces preserves existing Markdown hard breaks.
No proof or publication source file was changed by this referee.
Run `shasum -a 256 -c SHA256SUMS` here to validate this retained evidence.
