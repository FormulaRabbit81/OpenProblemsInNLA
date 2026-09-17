# Original target and proposed Lean boundary

The complete retained original page is `sources/canonical/README.md`, from
`ajt60gaibb/OpenProblemsInNLA` at
`ebdf2f34dc7690d8e323faaeb40d6dcc30c851ff`, canonical path
`matrix-inequalities-and-norms/MI-13/README.md`. Its SHA-256 is
`20a8326f71cf7eba180b3cb956cc7c374298823ceb6aae8be72489d49c86f730`.
This is a historical source snapshot, not a claim about a newly queried head.

| Original object or quantifier | Exact proposed Lean interpretation |
| --- | --- |
| Every integer `m,n ≥ 2` | `{m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)` |
| Complex rectangular A,C and B of opposite shape | `A C : Rect m n`, `B : Rect n m` |
| Frobenius norm | `frobeniusNorm A = ‖flatten A‖` in `EuclideanSpace ℂ (Fin m × Fin n)` |
| Euclidean operator norm | `spectralNorm A = ‖euclideanCLM A‖` between the genuine Euclidean vector spaces |
| Decreasing singular values σ₁,σ₂ | `singularValue A 0`, `singularValue A 1`, directly from `LinearMap.singularValues` |
| Actual rectangular products and subtraction | Lean's matrix products and subtraction in `A * B * C - C * B * A` |
| Exact universal coefficient | Literal real coefficient `2` in `canonical_rectangular_bound` |
| All zero and deficient ranks | No nonzero, invertibility, rank, distinctness, or genericity premise in the final declaration |

`frobenius_semantics` separately proves the entry sum and real trace identities
needed to match the printed norm. `operator_norm_semantics` separately equates
the CLM norm with the first actual singular value. `singular_values_gram`
connects each in-range squared value to the actual sorted Gram spectrum;
nonnegativity, order and zero extension have their own visible contract.
No convenient norm or spectrum is substituted by a definition with a chosen
answer. The positive-index set and `GramBasis` refer to those actual values.

The declaration-to-obligation map is the numbered 36-item pre-code plan, with
the exact headers and their hashes in `STATEMENT-HEADERS.json`. In grouped form:

| Challenge declarations | Obligation |
| --- | --- |
| 1–5 | Genuine norm and ordered singular-value semantics |
| 6–11 | Full actual SVD, including zero values, by partial-index extension |
| 12–13 | Unitary invariance of both norms and all singular values |
| 14–19 | Correct Hilbert–Schmidt commutator CLM, adjoint, J identities, Rayleigh maximum and nonzero functional-kernel eigenvector |
| 20–24 | Exact scalar coefficient bounds, canceled SVD coordinate estimate and full internally proved refined commutator theorem |
| 25–28 | Kernel LeanCert half certificate, exact unit-circle lift, every contraction's two-unitary average and squared Frobenius averaging |
| 29–31 | Exact unitary-middle identity, contraction bound and unrestricted square result |
| 32–34 | Actual block product, both norms and every zero-extended singular value preserved by padding |
| 35 | The complete original rectangular inequality, without any extra premise |
| 36 | Genuine 2×2 sharpness values, a normalization check rather than a substitute for the target |

The repository's reduction invokes Audenaert's existing refined commutator
theorem. Our proposed formal proof must discharge declaration 24 internally;
it may not add it as an axiom or a final hypothesis. The finite J/Rayleigh
argument in the retained route provides that planned internal replacement.
The repository pads into `max(m,n)`; this draft instead uses `m+n`, putting A,C
in the upper-right block and B in the lower-left block. The dimension-independent
square bound has the same constant, but all semantic padding identities remain
explicit proof obligations. Algebraic block multiplication alone is insufficient.

Both intermediate empty dimensions and the zero top-eigenvalue branch need
care. The final target retains its original lower bound two. Generic SVD,
norm and padding statements include empty spaces where meaningful; no global
`Nonempty` section instance silently restricts them. Scaling a middle matrix
must split B=0 before dividing by its actual operator norm. Normalized singular
images are only required to be orthonormal on the strictly positive subset;
zero singular images are proved zero separately.

This is a proposed boundary, not an immutable freeze or a completed proof.
