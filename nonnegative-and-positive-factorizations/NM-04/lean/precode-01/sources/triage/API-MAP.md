# Pinned source inspection and reuse map

All source paths and bytes are bound in `SOURCE-AND-SEARCH-EVIDENCE.json`. Searches are read-only `rg` calls with complete stdout/stderr retained. An unsuccessful bounded search means no match for those words in those directories, not proof that no equivalent result exists anywhere. No API below was compiled or tested during triage.

Pinned versions copied from exact upstream MF-07: Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The public MF-07 lakefile builds Solution. The older preparation lakefile builds Challenge and must not be reused as publication configuration.

## MF-05

| Published module or primary file | Reuse and boundary |
|---|---|
| MF07/Definitions | Actual Euclidean operator norm, reversed-list products, word membership, supremum word growth and infimum of positive-index roots; no new abstract radius oracle. |
| MF07/MatrixBasics | Spectral-norm multiplication, scalar multiplication and continuity; list/finite-product bridges. |
| MF07/CompactGrowth | Nonnegative growth, attained maxima, family norm bounds and `family_growth_submultiplicative`. Valid for arbitrary nonempty compact families. |
| MF07/RootSemantics | `rootGrowth_nonneg`, `rootValues_nonempty`, `rootValues_bddBelow`, `jointSpectralRadius_le_root`, `rootGrowth_pow`, and `familyGrowth_mul_le_pow` have general usable hypotheses. `radius_one_root_limit` and `radius_one_semantics` explicitly assume or characterize radius one; they are insufficient for arbitrary zero radius. |
| MF07/ProductEnvelope | `envelopeValues`, `productEnvelope`, bounds, norm axioms and generator bound work with arbitrary positive discount and a supplied exponential word bound. This is the main norm constructor for the perturbation step. |
| MF07/QuantitativeComparison | Public `quantitative_comparison` bounds growth by `d*s^(d-1)*(1+2*d^2*familyNorm(M)/s)^n`, for `s>=1` and radius one. Positive scaling/identity-adjunction must be proved before it handles arbitrary radius. |
| MF07/RoundedNorm and underlying Auerbach/SingularCoordinates/triangular modules | These supply the hard geometric argument behind that public comparison. Prefer importing the exact existing theorem over copying and re-proving these modules. The old preparation versions have several elaboration repairs absent; the exact published files are retained. |
| Mathlib/Order/ConditionallyCompleteLattice/Basic | Generated dual `exists_lt_of_csInf_lt`, conditional infimum bounds, and positive root-value nonemptiness select a good finite block. No positivity of every word norm is necessary. |
| Mathlib/Analysis/SpecialFunctions/Pow/{Real,Continuity} | Nonnegative real powers, inverse-natural exponent identities and continuity in a fixed positive base support scaling, `K^(1/n)->1`, and optimization. The route avoids logs of zero growth. |
| Mathlib/Topology/MetricSpace/HausdorffDistance | `IsCompact.exists_infDist_eq_dist`, `infDist_le_hausdorffDist_of_mem`, `IsClosed.hausdorffDist_zero_iff_eq`, and the Hausdorff triangle inequalities. Their finite-distance/nonempty hypotheses must be discharged for spectral images. |
| LeanCert/Tactic entry points; MF07/Numerical example | Published code uses `set_option leancert.trust "kernel"` and `interval_decide (trust := kernel)`, followed by explicit trust assertions. Its exp-one bound is actually consumed by MF-07's binomial estimate. MF-05 must likewise consume its chosen certificate, not merely import this example. |

The generalization route deliberately avoids changing accepted MF-07 files. Importing a reused closure still requires the normal source-matched local output policy. This packet did not authenticate or reuse any `.olean` output and cannot certify a new local build.

## NM-04

| Primary file | Available result and remaining obligation |
|---|---|
| Topology/Order/Compact | `IsCompact.exists_isMinOn`; `ContinuousOn.exists_isMinOn'` and continuous coercive variants. A concrete closed finite-dimensional box and mean-zero hyperplane make the minimization route explicit. |
| Topology/MetricSpace/ProperSpace | Compactness infrastructure for closed balls in finite-dimensional real spaces. Rectangular dimensions remain variables. |
| Analysis/SpecialFunctions/Log/Basic and Log/Deriv | Strictly positive row sums justify log continuity and `HasDerivAt.log`/`HasFDerivAt.log`; the actual derivative factor is the reciprocal of the positive row sum. |
| Analysis/SpecialFunctions/ExpDeriv | `Real.hasDerivAt_exp`, `HasFDerivAt.exp`; ordinary finite-sum derivative rules handle the log-sum-exp functional. No interval approximation of that functional is proposed. |
| Analysis/Calculus/LocalExtr/Basic | Fermat's theorem `IsLocalMin.hasFDerivAt_eq_zero` and its one-dimensional formulation, applied to actual mean-zero lines. This avoids an assumed Lagrange-multiplier theorem or constraint-gradient oracle. |
| Analysis/Convex/DoublyStochasticMatrix | Concrete square doubly stochastic definitions exist, but they are not rectangular positive diagonal scaling. Do not treat them as a Sinkhorn existence result. |
| LinearAlgebra/Matrix/Determinant/Basic | Column/row multilinearity, `det_updateCol_add`, scalar and finite-sum variants, zero determinant for dependent/repeated columns, and `det_submatrix_equiv_self`. Build universal singular-valid identities rather than expanding an arbitrary determinant. |
| LinearAlgebra/Matrix/Adjugate | `adjugate_fin_succ_eq_det_submatrix` supplies exact cofactor signs; adjugate multiplication and nonzero-kernel-vector determinant consequences support the final argument. |
| LinearAlgebra/Matrix/Charpoly/Coeff | `det_piecewise_one_eq_submatrix_det` and `coeff_det_one_add_X_smul_eq_sum_minors`; its proof uses the alternating multilinear map's `map_add_univ`. This is a direct structural template for the weighted diagonal/principal-minor expansion. The weighted version with arbitrary vanishing gamma/delta still needs proof. |
| LinearAlgebra/Matrix/SchurComplement | The scalar distinguished block x is invertible because x>0, so Schur determinant identities are applicable there. However `det_add_replicateCol_mul_replicateRow` explicitly assumes `IsUnit A.det`; its documentation TODO asks for the singular-valid adjugate formula. A proof for all minors cannot use that theorem without addressing singularity. |

The bounded whole-Mathlib search found square doubly stochastic/Birkhoff definitions and semistandard tableaux, but no result named Sinkhorn or matrix scaling. A separate Analysis/Topology search found no Brouwer/Schauder fixed-point entry under those words. The proposed scaling proof uses neither. The retained `NegMulLog` file demonstrates strict convexity of `x*log x`, but the final recommended route avoids the longer boundary-entropy argument and does not depend on that lemma.

## Rejected alternative MF-03

The complete manuscript's finite checks for m<=15 are not the full all-orders Padé theorem. Its symbolic tail route relies on a Schur-function/Jacobi–Trudi identity, positive infinite-alphabet limits and the cosh product coefficient interpretation. The pinned tableau file has the basic semistandard-tableau structure and highest-weight example, but the recorded search found no Jacobi–Trudi/Schur-polynomial theorem under those names. These are larger new foundations than the preferred second track's finite cofactor algebra. No finite-check surrogate is recommended.

## Future project structure

Use the accepted campaign's pinned Schiffer/Forsythe Challenge examples, Tau Ceti rubric snapshots, Comparator contract schema, formalization metadata schema, and per-target package structure during statement preparation. They are already retained in existing accepted packages; this triage does not claim a new exhaustive rubric/source review. Definitions and independent Challenge propositions must be frozen only after two nonauthor reviews and the parent's actual local elaboration. Final mathematical claims require both actual proof runs and exact source/contract correspondence; source searches alone establish neither.
