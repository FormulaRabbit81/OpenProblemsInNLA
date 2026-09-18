# Selected pinned primary APIs and new work

Mathlib is fixed at `0df444a360eaa60ab8c11dca51a86af692955474`, Lean at 4.33.1, and LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926`. `PINNED-API-BINDINGS.json` reauthenticates 19 prior literal-pin source bindings from the author's finite-route preflight, one prior adjoint binding from the MI-13 handoff, and two newly fetched, byte-matched sources. It records exact inspected ranges and local paths; no source or compiler cache was modified. This is not a full transitive proof audit.

| Ingredient | Actual pinned API/source | Formal work still required |
|---|---|---|
| Euclidean vectors and matrices | `PiLp.inner_apply`, `Matrix.toEuclideanCLM`, `Matrix.toEuclideanLin`, `LinearMap.toContinuousLinearMap` | Coefficient encoding, actual Toeplitz action, all norm transport. Never use the default matrix sup norm. |
| Actual finite-dimensional adjoint | `LinearMap.adjoint`, Adjoint:546; `adjoint_inner_right`, :588 | Positive-defect kernel equivalence and matrix conjugate-transpose transport. |
| Norm bounds | `ContinuousLinearMap.opNorm_le_bound`, `le_opNorm` | Compact-sphere attainment and norm/Gram-kernel equality. |
| Attained extrema and finite closedness | `IsCompact.exists_isMinOn`, `exists_isMaxOn`; `AffineSubspace.closed_of_finiteDimensional`, `FiniteDimensional.proper`; closed-set nearest-point existence | Nonempty compact balls/spheres, affine image closure, empty-complement branch. |
| Active-block coordinates | `Fin.cons` at Tuple/Basic:113; `Fin.snoc` at :515 | Distinct input/output decompositions and exact smaller boundary norm. |
| Actual matrix polynomial evaluation | `Polynomial.aeval`, AlgebraMap:257 | Normalized polynomial/residual equivalence and isometric conjugation. |
| Fixed-bound conjugate reflection | `Polynomial.reflect`, `coeff_reflect`, `reflect_reflect`, `reflect_map`, `reflect_mul`, `eval₂_reflect_mul_pow` | All degree hypotheses, conjugation, circle specialization, and coefficient-inner-product identity. |
| Common root and degree descent | `Polynomial.dvd_iff_isRoot`, `mul_divByMonic_eq_iff_isRoot`; `degree_mul'`, `degree_X_sub_C` | Zero summands, m>=1, repeated factor removal, reassembly without dividing on the circle. |
| Coprimeness | `IsCoprime`, `mul_left`, `dvd_of_dvd_mul_left` | Explicit Schur Bezout reconstruction. |
| Complex factorization | proved `Complex.isAlgClosed`, `IsAlgClosed.splits`, `card_roots_eq_natDegree`, `Polynomial.Splits.eq_prod_roots` | Reciprocal reflection of the full root product, inside/outside multiset split, and positive scalar normalization. |
| Root multiplicities and circle identity | `roots_mul`, `roots_C_mul`, `roots_multiset_prod_X_sub_C`, `eq_of_infinite_eval_eq` | Keep multisets; supply circle infinitude. No root-isolation oracle. |
| Real separation | `geometric_hahn_banach_point_closed`, Separation:225 | Compact real-convex image from scalar factorization, real-functional coordinate representation, and quantitative descent. |

The full finite Schur, weighted factorization, simultaneous complex preservation, and Toeplitz minimax results are NOT supplied by these ingredient APIs. The bounded negative searches in the referenced author/referee packets found no matching ready-made foundation in their recorded roots; this is not a global semantic nonexistence claim. They remain substantive proposed proof obligations.

Some Challenge contracts package semantic specializations of existing APIs. Implementations should reuse those APIs, not reprove library facts. The interfaces make the actual norm/degree/attainment meaning visible to Comparator and are consumed by the full original target; no standalone claim of mathematical novelty is made for wrappers. The optional circle-integral and compact-convex-hull machinery is unnecessary for the chosen complete finite route.

The sole planned numerical certificate is the exact scalar half positivity in kernel mode. Its consumer is `descent_step_bounds`, because both concrete step definitions multiply a strictly positive minimum by one half. All other positivity and cancellation use hypotheses symbolically. No certificate or proof has been executed.
