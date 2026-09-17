# MF-07: bounded reuse and API inspection

No proof has been implemented or imported. The following references were read
to design the statement boundary; hashes and complete private source snapshots
are recorded separately. Read-only inspection is not a successful elaboration.

* Existing MF-12 uses the actual real Euclidean operator norm and chronological
  reverse-list product. MF-07 follows those definitions over complex matrices
  and arbitrary `Set` families. It does not import MF-12's finite-generator
  theorem or replace compact families by finite ones.
* MF-24 and MF-22 explicitly use `Matrix.toEuclideanCLM` for the complex spectral
  norm. The pinned Mathlib `Analysis/CStarAlgebra/Matrix.lean` defines this as
  the actual Euclidean continuous-linear-map equivalence and provides algebra
  and operator-norm APIs. Definitions in this draft use it directly.
* `Data/List/OfFn.lean` provides the finite-sequence/list interface used by the
  final all-word statement, with `ofFn_get` and `forall_mem_ofFn_iff` available
  for future correspondence proofs.
* Pinned `Analysis/Subadditive.lean` supplies the logarithmic Fekete route via
  `Subadditive.tendsto_lim` with its actual bounded-below premise. Radius-one
  positivity, root semantics and the conversion from multiplicative growth
  remain proof obligations; no limit is supplied as an axiom or trusted field.
* Pinned finite-dimensional norm and singular-value files were inspected for
  compactness, norm-equivalence and antitone singular-value infrastructure.
  That inspection did not locate a ready-made full norm-rounding theorem or
  complete SVD constructor in those files. A bounded filename search also found
  no Auerbach-named module. This is not a claim about every Mathlib theorem.
  The maximal-determinant argument, the needed coordinate construction and
  the quantitative triangular comparison remain substantial implementation
  work. They are explicit independent contracts, not hidden assumptions.
* The pinned exponential file uses `Real.add_one_le_exp`, `Real.exp_nat_mul`
  and monotonicity APIs. The intended variable-power argument is symbolic;
  the separate certificate supplies only `exp 1 ≤ 3`.
* Existing IE-13 and MI-04 certificate modules were read for their explicit
  kernel-mode LeanCert pattern and genuine downstream use. MF-07 has no
  certificate code yet and does not count a dependency pin as a certificate.
* The complete retained Schiffer Challenge was read for independent statement
  organization. Forsythe's `NUMERICAL_TARGETS.md` and `Challenge.lean` at
  `8d1b0c0545a77b40245e84705aa7d273e6c81e62` were read for numerical-first and
  Comparator structure. No theorem from either project is imported.

Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert to
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Lean to v4.33.1. The lockfile
reuses the existing campaign's exact dependency entries; only the root package
name changes. This does not establish that the new draft elaborates.
