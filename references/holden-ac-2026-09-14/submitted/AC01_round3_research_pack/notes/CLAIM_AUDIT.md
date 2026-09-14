# Claim and dependency audit

This is a partial mathematical research derivation. A successful Python run is not a proof-assistant certificate for the complete argument.

| Claim | Basis | Scope and limitation |
|---|---|---|
| Initial Fourier exchanges and composite | Report Section 3, rational Fourier maps, exact cancellation, archived round-two coefficient checks | Reproved here; the source bound is 330, not an assumed exact spectral value |
| Non-coordinate isotropic core | Two explicit 3-by-3 forms; nine zero Gram entries; rational split bases | Exact finite rational identity |
| Odd-size split extension | Explicit basis in Section 5 | All positive odd sizes; finite examples are supplementary |
| Retained tensor is P tensor Z | Direct coefficient computation in Section 6 | Exact tensor identity; no conjectural relative entropy inequality |
| Value lower bound for Z | Injective tight-support weights and uniform marginals | Uses the external three-tensor tight-support theorem |
| Mixed-state extraction | Active-quotient proof, rational paired-complement construction, separated-parameter extraction | Actual coordinates are not replaced by active dimensions |
| Bound 3.876919161 | Three finite extraction stages, spectral duality, tight-support estimates, exact integer-cube enclosures | Derived bound on asymptotic rank, not on omega; not independently refereed |
| Stored P^2 plus C_10 degeneration | Complete 20-by-25 Laurent row map and all coefficient checks | Fully finite example; does not alone prove the asymptotic bound |
| Candidate 3.652 for all finite binary trees | Product-envelope induction and exact leaf/coefficient inequalities | Only the explicitly defined fixed-seed scalar tests; not a spectral point or rank lower bound |
| Omega equals two | Not established | The required rank asymptotic remains missing |

## Exact versus general verification

The coefficient checker expands all nonzero source terms and accounts for all possible ordered output coefficients. An absent sparse coefficient is zero by exact accumulation. It does not use a random sample, numerical rank tolerance, or a small floating-point degeneration parameter.

The all-size construction relies on a mathematical proof. Its subsequent matrices can be generated in principle by rational linear algebra, but the largest ones were not materialized. The tree obstruction covers all finite trees because of the proved envelope inequality; the thirty finite tree tests merely supplement that proof.

## External mathematical inputs

Strassen's asymptotic spectral duality and tight three-tensor subrank theorem are stated in the report, with precise primary-source references. Neither is formalized by the supplied Python program. The matrix-multiplication tensor-rank equivalence is used to state the missing target, not as a shortcut to assert that it has been attained.

## Safe interpretation of the numerical bounds

The bound `3.876919161` is an upper bound on the asymptotic rank of the small CW tensor. It is not a finite-rank decomposition at that rate. The value `3.652` is a feasible assignment in a scalar relaxation, not a lower bound on the tensor's true asymptotic rank. The two numbers concern different kinds of statements and must not be combined into a claimed interval for the actual rank.
