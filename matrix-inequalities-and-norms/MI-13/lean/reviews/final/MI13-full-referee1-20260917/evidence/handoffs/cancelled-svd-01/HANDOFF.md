# MI-13 canceled SVD candidate 01

New source: `NLA/MI13/CancelledSVD.lean`, SHA-256 `421d9632779e21ae956c468f5f6212ebda38ef5ae00a514406ab545b9987217a`.

This is an authored, **locally unrun candidate** for exactly the frozen `svd_corner_functional` and `cancelled_svd_bound` contracts. Their headers match the accepted Challenge byte-for-byte. Root owns the serial local compiler, any repair, subsequent independent proof review, and final GitHub Comparator/kernel/sandbox checks. No Lean, Lake, cache command, Git command, or publication action was performed by this author. No target count changes.

The author is `/root/mi13_statement_freeze`, who previously prepared MI-13 freeze packaging and independently reviewed other bounded MI-13 modules. Those historical reviews do not review or approve this newly authored source. Another nonauthor referee must review this module. The earlier packet scopes remain unchanged.

The source imports only `ElementaryBounds`, `UnitaryInvariance`, and `CommutatorEigenspaces`, with their existing project dependencies. The current `UnitaryInvariance.lean` digest `bd825d92218cf9b947bad95d34ba6f45bc37b29a0fa5246cd929a9a00889dae8` matches the successful comment-refreshed local 40 command and the current shared source. The copied local 40 context establishes that dependency identity; it is not evidence that this new candidate compiled.

The proof is factored into small steps:

1. `firstEntryLinear` bundles the actual total selector. For positive dimension it evaluates the first entry; in dimension zero it is the zero map. Composing it with `LinearMap.mulLeftRight` and the existing `commutatorLinear` proves the exact functional contract without a dimension or unitarity premise.
2. `svd_commutator_transform` uses the supplied exact SVD equality by congruence, keeping `singularDiagonal X` fixed while replacing the outer matrix. Ordered multiplication and `U*U = V*V = 1` give `U*[X,Z]V = Σ(V*ZV) - (U*ZU)Σ`.
3. `svd_diagonal_entry` makes the scalar entry formula explicit. `cancelled_svd_entry_bound` treats the first pair separately using its vanishing. Every other pair uses the existing complex `two_coordinate_bound` and ordered `off_corner_coefficient_bound`. The remaining weight is a sum of squared entry norms and is nonnegative.
4. `cancelled_svd_diagonal_bound` sums those inequalities over the complete pair of finite index sets and rewrites the genuine Euclidean Frobenius squares through the already proved entry-sum identity.
5. `cancelled_svd_bound` transports the commutator and both conjugates of `Z` through actual unitary Frobenius invariance. The two conjugates have norm `‖Z‖_F`, so their squared-norm sum gives exactly the frozen factor two.

The proof does not divide by a singular value or by the norm of `Z`; zero matrices, deficient rank and repeated or zero singular values require no extra case hypothesis. The frozen square bound retains `r ≥ 2`. The only helper dimension premise is positivity when choosing the actual first index. The functional itself includes the empty dimension. No supplied norm bound, eigenvector, oracle, normality premise, extra axiom or weakened contract is introduced.

The candidate contains four helper theorems and one concrete helper linear map in addition to the two frozen contracts. There is no `change` or `show`; comments explain the first-entry branch and the concrete bundled-map evaluation. The finite matrix and scalar algebra is symbolic. No new numerical target or approximation is introduced, and the earlier exact-half certificate is not artificially made a premise of these two contracts. Its genuine averaging consumer remains in the separate existing proof route.

`PRIMARY-API.json` binds the actual pinned sources inspected for bundled multiplication/composition, matrix entry and diagonal-product formulas, associativity and distributivity, adjoint involutivity, finite-sum distribution and monotonicity, and finite-index equality. `IMPORT-CLOSURE.json` records all ten project modules, including this candidate. Lean remains 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`; the shared and frozen package revisions match.

The actual Python audit passed 112 metadata/header/hash checks and records 35 bindings. It checked all 13 frozen-file hashes, both exact contract headers, source scans, imports, pins, attribution, and unchanged existing dependencies during handoff preparation. The source sets kernel-mode LeanCert trust and includes `#print axioms` and `#assert_trust kernel` for both contracts. Those commands are present in the candidate; their success is not claimed before root runs Lean.

Only the new source and this handoff were written. The frozen Definitions, Challenge, numerical plan, earlier proof modules, shared cache and historical review packets were not edited. The immutable candidate snapshot preserves this first proposal if later compiler feedback requires a separate documented repair. George Stepaniants's Caltech CMS attribution is retained without an email, with Nobori, Audenaert and repository attribution preserved.
