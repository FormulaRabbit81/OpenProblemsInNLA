# SP-04 — independent exact-statement referee 2

**Verdict: APPROVE the frozen mathematical and numerical boundary below.**

Phase: pre-proof statement review. Date: 2026-09-15. Reviewer: OpenAI Codex GPT-6 AI agent `/root/existing_verification_audit`, independent of the statement author, numerical contributor and future proof implementers. I did not edit the canonical statement, frozen boundary or proof files. This review applies `docs/lean/REVIEW.md` and its adapted Tau Ceti fidelity, scope, correctness, API, reuse, documentation and attribution criteria. It is not external human review or an official Tau Ceti service verdict.

The canonical page remains **Solved**. The eleven deliberate Challenge placeholders prove nothing. No final source proof, Comparator run, Linux verification or status promotion is certified by this approval.

## Exact reviewed boundary

Published base: `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
`reviews/statement-inputs.json` SHA-256: `bd45a690495a0a396448925b057cf2d1e5368ba6dd2fab377f4598b5961ef7ef`.
I independently recomputed all ten hashes before and after the checks; every file matched:

| Input | SHA-256 |
| --- | --- |
| `NLA/SP04/Definitions.lean` | `6ec0afd466bfb054b9a46353f37a01e39333259e2579f21ae5fd52b5e9d57161` |
| `Challenge.lean` | `79aa3fe4ce1d75157f153b259660a8abd08cd8f0cecc7d0fad3ebcca0cf98381` |
| `NUMERICAL_TARGETS.md` | `e14351bfa611bf6f1d1c7302b0584866bb54074c9db3c1e8f43c1f5dee571290` |
| `comparator.json` | `d0783ec075a831cee2a501a46e02e42258b995f9fbf377dab1c749bba95457ff` |
| `lakefile.toml` | `1f4038f5e6c2f3ed9409d51f444f1ca2256b03a828d69b0dca855f61f2b082fd` |
| `lake-manifest.json` | `0b777416633b6ab6cecb4b739da1148251ec285a20225da94da6f72b56bddcab` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial/independent-exact-check.py` | `41729e1a69cb0b5e3aa314f6dfb4a427e16467edec5022de0ff29229b06123dc` |
| `reviews/initial/independent-exact-check.json` | `8333c86c264642f175a0134ccc085dbfd6b8051ee0ab1fdb08836e1d15e33873` |
| `reviews/initial/source-hashes.json` | `a5aa8f0e6f552ebd9045a18b623792a1af8155e5ba312685028776370dc210ea` |

I read the complete original README, all four proof sections and scope notes in the Markdown/TeX manuscript, the historical review, actual definitions, all eleven Challenge signatures, the entire numerical dossier and diagnostic implementation/output. The four original whole-file hashes in `reviews/initial/source-hashes.json` independently match the current files and published-base Git blobs. The historical normalized mathematical-block hash also independently matches `77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95`; it is not confused with a whole-file digest.

## Fidelity and nonvacuity

`Mat n` is the full real square matrix space. `Feasible X` is exactly `|det X|=1`, retaining both determinant components. `Stationary` uses the literal equation `Xᵀ*(U-X)=c•I`, and `stationaryPairs` contains every real matrix/multiplier pair satisfying it. No diagonal restriction, sign assumption on the multiplier or candidate enumeration occurs in these definitions.

`UniqueLeastStationary` first requires stationarity, then compares absolute multipliers against **every** stationary pair. A tie forces equality of both the matrix and multiplier. This is stronger than uniqueness of a numeric root and matches the canonical uniquely chosen-pair locus. `IsNearest` requires feasibility and the global distance inequality against every feasible matrix, so it expresses attainment at the selected matrix directly. Its negation via a strict feasible improvement does not rely on an unproved `sInf` convention.

The norm is literally the nonnegative square root of the sum of all squared entries. No default matrix/Pi operator norm is substituted. Both the diagonal and full-family counterexample signatures demand the **unsquared** strict Frobenius comparison, leaving the necessary square-root ordering bridge as a genuine proof obligation.

`RegularData U` requires nonzero determinant and no repeated roots in the actual real Gram characteristic polynomial. Root-list nonduplication would be insufficient for an arbitrary real polynomial with nonreal roots, but `UᵀU` is real symmetric/Hermitian. I inspected and independently typechecked the pinned `Matrix.IsHermitian.charpoly_eq`, `roots_charpoly_eq_eigenvalues`, `splits_charpoly` and spectral-theorem API context. They account for all eigenvalues over the reals with multiplicity. Thus this definition means genuinely distinct squared singular values. The public `regular_svd` theorem must establish it for every admissible genuine SVD; it is not assumed from membership in the counterexample family.

`GenericSelectionRule n` permits an arbitrary nonzero polynomial in all `n²` real entries as its exception, then retains regularity, finite stationary set and unique selection as premises. `AllGenericSelectionRules` quantifies over all natural dimensions at least two. `generic_counterexamples` provides a dimension-three counterexample outside **each** nonzero nine-variable polynomial, and `SelectionFails` explicitly proves every regularity/finiteness/selection premise. Thus no generic assumption is vacuous or hidden. Every proper real algebraic exception is contained in a nonzero defining polynomial's zero set. A three-dimensional diagonal example alone would be inadequate; the required nonempty open family and avoidance theorem are in the full nine-dimensional matrix topology.

The family is defined solely by three strict negative products of characteristic values at squared rational endpoints. It contains no SVD or failure conclusion as an assumption. Product negativity is precisely enough for three IVT brackets without presupposing sign orientation. The disjoint positive intervals give three distinct positive roots of a monic cubic, hence all Gram eigenvalues; the actual SVD and regularity exports preserve the spectral bridge. `HasSVD` means a literal factorization with both orthogonality equations, allowing either orientation.

## All eleven exports

I matched these names, order and types against `comparator.json`; all eleven are included and `definition_names` is empty:

1. `numerical_bounds`: four exact closed real inequalities, including the product bound actually intended for the scalar exclusion.
2. `diagonal_stationary_iff`: both directions for every admissible real triple, arbitrary real matrix and arbitrary real multiplier; all three scalar quadratics and absolute product one.
3. `diagonal_counterexample`: every admissible triple, an actual `0<t<13/25`, the literal selected matrix and multiplier `-t`, global unique least pair, and literal feasible sign-flipped improvement in the actual norm.
4. `diagonal_finite`: the entire stationary-pair set, with no multiplier cutoff or determinant-sign restriction.
5. `orthogonal_transport`: every dimension and both real orthogonal factors, feasibility equivalence, norm equality and stationary equivalence with the same multiplier. The eventual proof must use its inverse transformation to transport whole sets and uniqueness.
6. `spectral_family`: full-space openness, unchanged exact rational sample membership and actual admissible SVD for every family member.
7. `regular_svd`: actual invertibility and simple real Gram spectrum from every admissible SVD.
8. `open_family_counterexamples`: every member has all properties in `SelectionFails`, including full-set finiteness and strict improvement.
9. `algebraic_avoidance`: every nonempty open full matrix set and every nonzero polynomial in all nine entries.
10. `generic_counterexamples`: complete failure outside each proposed proper polynomial exception.
11. `canonical_counterexample`: the full negation `¬ AllGenericSelectionRules`.

## Independent arithmetic and mathematical bridge checks

My independent reconstruction uses exact `Fraction` arithmetic, an explicit tensor-entry definition and permutation-sum determinants; it does not import or execute the contributor's implementation. The six Gram values have common denominator `10^18` and numerators

`[-1937653044525, 905786883351, 648098176275, -649206984825, -910443880269, 1954285183575]`.

Their signs are `-, +, +, -, -, +`, and all three paired products are strictly negative. The four actual Challenge inequality margins are respectively `3/1250`, `11/18`, `1039/15625`, and `7/400`, all positive. I also checked the rationalized square-root factor `16/9`, its resulting root-difference bound `1/72<1/50`, and the endpoint test `-1/50`.

Independently reconstructed the optional rational stationary example: both determinant signs, all three exact stationary equations, strict squared improvement, nonzero tensor eigenvector with last coordinate one, eliminant vanishing at its actual multiplier and nonzero eliminant evaluation at zero. These diagnostics agree with the submitted record; I separately reran its copied script and obtained byte-identical JSON. The optional example remains diagnostic and does not replace the universal source-family proof or the original sample used for openness.

I independently checked the all-real mathematical argument required by the boundary: unrestricted stationary diagonalization via Gram commutation; exclusion of every nonnegative multiplier up to `13/25`; existence of an interior negative selected multiplier; comparison of all eight root patterns, including ties; exact feasible sign reversal; and two-sided SVD transport. The source's asymptotics for other negative branches are unnecessary for the selected-pair claim and may be omitted without weakening any export.

The additional finite-set argument is sound: the triple companion tensor has an eigenvector with final coordinate one and eigenvalue equal to the product of the scalar roots, necessarily `+1` or `-1`. Hence every multiplier is a root of `det(K-I)det(K+I)`. At zero this polynomial evaluates to `1-(s₁s₂s₃)²≠0`. Its root set is finite; each fixed multiplier permits only finitely many scalar triples because the three quadratics are monic. This must be combined with the all-stationary diagonal reduction and inverse SVD transport in the eventual proof. No full resultant expansion or numerical root search is required.

## Reproducible checks, API and attribution

Created a fresh external project at `/private/tmp/nla-campaign-existing-review/SP04-statement-build`, copying the frozen project source without its `.lake/build`. Reused only the existing pinned dependency package cache. With Lean 4.33.1, `lake build Challenge` exited zero and rebuilt Definitions and Challenge; exactly eleven expected `sorry` warnings occurred, all in Challenge. The cache's Mathlib and LeanCert Git revisions match the manifest and have clean status.

The independent `BoundaryAPI.lean` only prints definitions, checks existing Mathlib statements and synthesizes the actual matrix topology; it adds no mathematical proof. It compiled successfully. The three printed definition axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. These checks do not substitute for final theorem trust audits. The future Comparator manifest permits only those same three axioms.

The explicit Frobenius definition avoids the multiple matrix norm instances documented by pinned Mathlib. Existing Hermitian spectral, polynomial, continuity and finite-dimensional APIs support the proposed proof without custom spectral axioms. Transparent problem-specific predicates are appropriate. The project retains the campaign's pinned dependency and Challenge/Solution separation; actual Comparator replay and LeanCert kernel-mode consumption remain final implementation obligations.

Headers attribute formalization to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, disclose substantial OpenAI Codex assistance, and preserve Matthew J. Colbrook's original mathematical credit. No new contact email is added. Original source files, including their historical attribution, are unchanged. The dossier accurately distinguishes preparation from formal verification.

## Evidence and remaining gates

Evidence: [`statement-referee-2-evidence/review-evidence.json`](statement-referee-2-evidence/review-evidence.json), SHA-256 `7ca03996e3e3d521438790c35e360431014a84521f6ae306956efa667696ffc6`. It records exact input/source hashes, commands, revisions, independent arithmetic, copied-diagnostic replay, API output and fresh build log hashes.

No requested changes or unresolved statement-level findings remain. Approval is limited to these exact bytes. Implementation must still prove all eleven complete exports, consume the numerical certificate with LeanCert in explicit kernel mode, receive independent final source reviews, pass default-kernel Comparator correspondence and permitted-axiom checks, and complete reproducible Linux verification before any `Lean verified` status.
