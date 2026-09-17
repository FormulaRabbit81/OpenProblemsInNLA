# Verification record — 17 September 2026

**Result: PASS.** Two separate mathematical review agents and a document-review agent checked the submitted scope. This is informal automated review, not external human peer review or formal verification.

## Mathematical review and certificates

- `/root/review_border_lemma`: [final source review](border-review.md), including the simultaneous border lemma and all explicit appendix identities.
- `/root/review_existing_mf14`: [final source review](continuation-review.md), including the continuation, exact Jacobian, full ambient closure and dimension-based upper bound.

Both reports bind their findings to `proof.tex` SHA-256 `c987a6ac3532b50a8241702612c05d951d2a7d9b467a14aec922ea3c83d3de88`.

The three bundled programs passed with both `python3 -B` and `python3 -O -B`. Each normal execution produced a certificate byte-identical to its optimized execution. All checks use explicit exceptions. Commands are in the [submission README](../README.md#reproduction).

| Check | Result | Evidence |
| --- | --- | --- |
| Third-product identity, full 12-by-12 differential minor, determinant degeneration and lower basis | PASS, exact multivariate integer arithmetic | [Log](verify_border_independently.log), [certificate](symbolic_certificate.json) |
| Untruncated simultaneous jets, all analytical derivative columns, rational and modular elimination | PASS; determinant 256 | [Log](independent_degree44_jets.log), [full matrix](independent-degree44-certificate.json) |
| Whole-circuit interpolation and independently multiplied inverse modulo 3 | PASS; determinant 256 | [Log](supplied_interpolation.log), [certificate](interpolation_certificate.json) |
| Cross-method comparison | All 2,025 Jacobian entries, parameter order, parameter point and determinant agree | The two matrix certificates above |

## Repository checks

Base: `origin/main` at `d348d7471e2ff881ae30fb8a9c40323a61cd383a`.

| Command | Result |
| --- | --- |
| `python3 tools/validate_problem_ids.py --base-ref origin/main` | PASS, 217 permanent IDs |
| `python3 tools/update_catalog.py --base-ref origin/main` | PASS; 42 Open, 70 Partially resolved, 60 Solved, 45 Lean verified |
| `python3 -B -m unittest discover -s tests -p 'test_problem_ids.py' -v` | [17 tests passed](test_problem_ids.log) |
| `python3 -B -m unittest discover -s tests -p 'test_problem_statuses.py' -v` | [3 tests passed](test_problem_statuses.log) |
| `python3 tools/format_math.py --check` | PASS; 0 pages need formatting |
| `python3 -B -m unittest discover -s tests -p 'test_format_math.py' -v` | [16 tests passed](test_format_math.log) |
| `python3 -B -m unittest discover -s tests -p 'test_render_math.py' -v` | [11 tests passed](test_render_math.log), rerun after the MF-14 page-layout change |
| `python3 tools/render_problems.py MF-14` | PASS, no reported overfull boxes or missing characters |
| `git diff --check` | PASS |

The [preservation record](preservation.json) confirms byte equality of the original mathematical statement and of the complete ID registry against the published base. The 11 September Colbrook archive is unchanged. The open count changes from 113 to 112; no problem is renumbered, removed or replaced.

## Document inspection

The proof was compiled twice with XeLaTeX (TeX Live 2025), with no warnings in the final build. The canonical entry was rebuilt using the repository renderer. Reviewer `/root/package_checks` rendered and visually inspected all six proof pages and both canonical pages using PDFKit.

No clipping, overlap, missing glyphs or broken equation references were found. The proof's byline and PDF metadata identify Marcus Webb, The University of Manchester, with date 17 September 2026. The canonical PDF keeps the complete retained problem statement together on page 2. The small renderer change affects only MF-14's page breaks.

Final PDF SHA-256 values:

```text
382e9b7e27b24b9800e9102b3483b8beebe32329e8eab50fe31c46e2d94d51b8  proof.pdf
0932da3ca9d27cba8eb70de2f78290bfa5f623ae64949f4f67f31681ce95416a  matrix-functions-and-stability/MF-14/problem.pdf
```

The [manifest](manifest.json) records the prepared files. No remote branch or pull request was published during preparation.
