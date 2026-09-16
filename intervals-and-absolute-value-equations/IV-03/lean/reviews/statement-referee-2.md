# IV-03 independent statement referee 2

- Phase: statements before proof implementation.
- Reviewer: `/root/new_target_screen`, independent OpenAI Codex AI agent.
- Independence: I did not author or modify this IV-03 mathematical boundary.
- Date: 14 September 2026.
- Verdict: **APPROVE** for the statement gate, specific to the bytes below.
- Protocol: repository `docs/lean/REVIEW.md`, read and applied. This adapts Tau Ceti review responsibilities; it is not an official Tau Ceti run, endorsement, or human peer review.

## Material inspected

I read the entire canonical IV-03 README, complete authored manuscript `references/colbrook-intervals-2026-09-11/manuscripts/IV-03.tex` at commit `deb549fa9ddd6b119e6c59016f268237e645dfa2`, the numerical plan, all definitions, all four Challenge signatures, source provenance, build receipt and actual successful build log. I independently recomputed every file digest in the supplied typecheck receipt and both source digests from the pinned Git objects; all matched. Source-authored historical review labels were not treated as formal evidence.

## Fidelity and scope findings

The canonical dimension range is all n≥1; both `TwoSignCriterion` and `nSquaredCriterion` retain it. Endpoints are arbitrary real matrices satisfying only entrywise L≤U. The interval subtype predicate has both closed inequalities at every independent entry. Zero widths, zero entries, reducible matrices and point intervals remain included. No regularity, invertibility of interval members, determinant sign, symmetry or strict positivity has been added as a premise.

`IsInverseM A` means actual `IsUnit A`, entrywise A≥0, and nonpositive off-diagonal entries of the actual total matrix inverse. The invertibility guard is crucial and present. For a matrix-ring unit this inverse is the genuine two-sided inverse; the predicate is exactly the canonical definition of the inverse of a nonsingular Z-matrix with nonnegative inverse. It does not accidentally admit singular matrices because of Lean's totalized inverse. The lack of an explicit positive-diagonal condition is faithful to the canonical definition, not an omission of a supplied assumption.

`center`, `radius` and `signVector` are exactly C=(L+U)/2, R=(U−L)/2 and the vector with −1 only at the selected index. `vertex` has the correct minus/plus sign, row and column indices, and scalar entry products. `vertex_formula` requires its equality with actual D_i R D_j multiplication, and `vertices_admissible` requires membership in the actual full interval. All ordered pairs and both signs occur in the final criterion. Duplicates at small dimensions or zero widths do not alter the universal test.

The stronger `nSquaredCriterion` uses precisely the negative-sign vertices of the complete source Theorem 1. It is required as a conclusion, not assumed in the two-sign theorem. Its complete equivalence for every dimension and every ordered box implies the original two-sign equivalence. No numerical-only certificate, source lemma assumption, or definition hides the target conclusion. The all-dimensional derivative/Schur-complement/adjugate arguments remain substantial future proof obligations.

The numerical plan accurately identifies the delicate points of the supplied proof: true base dimensions one and two, proper principal submatrix induction, sign-controlled Schur-complement monotonicity over the entire box, and adjugate completion to obtain determinant positivity without presuming regularity. Exact symbolic reduction is appropriate; no artificial interval grid is needed. Excluding the manuscript's operation-count discussion from the exported target is justified because the canonical question asks for the equivalence, not a machine-model complexity theorem.

Authorship records retain Matthew J. Colbrook as mathematical source author and Sidney Holden as the new AI-assisted formalization author. No proof completion or source endorsement is asserted.

## Mechanical checks and limits

The supplied build log records successful Definitions and Challenge builds under Lean 4.33.1, with exactly four deliberate sorry warnings. I independently reran the current `lake build Challenge`; it exited zero, incrementally replaying Challenge with the same four warnings. The independent log is `statement-referee-2-typecheck.log`. This replay is not described as a clean rebuild. Source and boundary hashes were checked independently afterward.

This approval is for well-scoped statements only. The four placeholders establish no mathematics. There is no inspected Solution, no all-export LeanCert/axiom audit, no actual Linux Comparator/default-kernel verification, and no negative-control run in this review. Comparator configuration must eventually cover all four declarations with no definition substitutions and only the standard logical axioms. The completed proof still requires independent final review and all mechanical gates before a Lean-verified claim. Material changes require rereview.

## Reviewed byte hashes

| Draft file | SHA-256 |
| --- | --- |
| `NLA/IV03/Definitions.lean` | `34d9726c54ec0b10005cb4225adf1c403a7109a0800b42c1f19865c1a897db2b` |
| `Challenge.lean` | `3e74a057fbe2181f3ac889f74df950cb7aea0e21a01bf4940418066894d8591f` |
| `NUMERICAL_TARGETS.md` | `8d4e594d33a3da2150d3c544e5142c071441f2427bac33aab052aa139818f58d` |
| `SOURCE_PROVENANCE.json` | `a764cd16583f1ae88d84872eeaf13153ab83c17ff4b3ca2c0a3426f866c6901d` |
| `statement-typecheck.log` | `bbd7e572158d282f6a6f824c80c09f209c7aac12690e29bb70181682c391fe03` |
| `statement-typecheck.json` | `9c8be0e79ef198f73b587c966c1b5c9cd776bbbdb6f9fb39c2344a3647ee1ce2` |
| `statement-referee-2-typecheck.log` | `e3b50a3f2d695003ff726ba2d845556cd79901ee543a463c4c8f051989546103` |
| `lakefile.toml` | `fbb15fb37659cbbde0fc85ece3194c7d7bb1469ce4488e979b9a180d3a6767ff` |
| `lake-manifest.json` | `d9a0ea4a2d128ac4d2700e3034e23105666a375aa5a4b9a65f839de18b4805ab` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

| Pinned source | SHA-256 |
| --- | --- |
| `intervals-and-absolute-value-equations/IV-03/README.md` | `c5c92b828ae968b01e53dab0e71b9adca662efe0075f8928606dc5e671c439d2` |
| `references/colbrook-intervals-2026-09-11/manuscripts/IV-03.tex` | `f09cb222b822704855031d18c971b3d61dbea4a371ee4547414c9e40500c3e98` |
