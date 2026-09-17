# MF-07: correspondence with the unchanged original target

Canonical source: upstream `ce47b5630bf3680d9211131c3a43825b022c139a`,
`matrix-functions-and-stability/MF-07/README.md`, complete Context and Problem
statement. Mathematical proof: Matthew J. Colbrook, *Uniform polynomial product
bounds and sharp Hölder continuity of the joint spectral radius*, Theorem 1,
Lemmas 3–4 and Proposition 5. The full manuscript was read; its separate MF-05
result is not part of this draft.

| Source object or quantifier | Formal object or required correspondence |
| --- | --- |
| Every integer d≥1 | `d : ℕ`, `hd : 1 ≤ d`; no upper bound on d |
| Complex d×d matrices | `Square d = Matrix (Fin d) (Fin d) ℂ` |
| Euclidean spectral norm | Norm of `Matrix.toEuclideanCLM`; never the default entrywise norm |
| Arbitrary nonempty compact family | `M : Set (Square d)`, `IsCompact M`, `M.Nonempty`; not a `Finset` |
| L is the largest generator norm | `familyNorm` is its actual supremum; `family_norm_maximum` proves attainment and every-generator domination |
| All products, allowing repeated generators | `WordIn` and arbitrary `List (Square d)`; `finiteProduct` uses `List.ofFn` for the final n-indexed formulation |
| Aₙ⋯A₁ | `matrixProduct w = w.reverse.prod`; `matrix_product_semantics` exports the empty and right-appended-generator identities |
| Maximum norm of length-n words | `familyGrowth`; `family_growth_maximum` proves exact attainment and universal upper bounds, including n=0 |
| JSR defined by the root limit | `jointSpectralRadius` uses the actual infimum over positive-length roots; `radius_one_semantics` must prove equivalence with `Tendsto (rootGrowth M) atTop (𝓝 1)` |
| A nonvacuous radius-one class | `identity_family_semantics` proves the identity singleton has every growth value and radius equal to one |
| One constant depending only on d | `growthConstant d`; the final existential is outside every family/word/length quantifier |
| Every n≥1 and every selection A₁,…,Aₙ | `∀ n, 1 ≤ n → ∀ A : Fin n → Square d, (∀ i, A i ∈ M) → …` |

The matrix topology used by `IsCompact` is the ordinary finite-dimensional
coordinate topology. The Euclidean operator norm is explicitly defined through
the continuous linear map; the norm inside the estimate does not depend on
which equivalent finite-dimensional norm supplies the topology.

## All eighteen independent obligations

| Declaration | Exact source/role |
| --- | --- |
| `matrix_product_semantics` | Chronological notation, Section 1 |
| `diagonal_inverse` | Actual inverse of a nonzero diagonal, Lemma 3 and Proposition 5 |
| `family_norm_maximum` | Canonical definition of L; compactness, not a supplied maximizing matrix |
| `family_growth_maximum` | Actual maximum over all words and elementary generator-norm bound |
| `family_growth_submultiplicative` | The root-limit foundation stated in Section 1 |
| `radius_one_semantics` | Proved infimum/root-limit equivalence at exactly the canonical radius and the consequence L≥1 |
| `identity_family_semantics` | Explicit nonvacuity and the genuine empty product |
| `approximate_extremal_norm` | First paragraph of Lemma 3; existence for every a>1, not an assumed extremal norm |
| `rounded_extremal_norm` | Remainder of Lemma 3, specialized to the original radius-one case; unitary coordinates, sorted positive scales and factor d |
| `triangular_damping` | Lemma 4, retaining full equal-weight diagonal blocks |
| `interspersed_product_bound` | Proposition 5's exact expansion by E-positions, with empty C-segments included |
| `quantitative_comparison` | Proposition 5 for every s≥1 and n≥0, at the canonical radius one |
| `scalar_family_growth` | The complete d=1 endpoint of Theorem 1 |
| `exp_one_bound` | One consumed LeanCert certificate used only to rationalize the explicit constant |
| `comparison_threshold_bound` | Theorem 1's symbolic threshold choice and exponential estimate, with all d,n,L quantified |
| `growth_constant_positive` | Required positive dimension-only constant |
| `radius_one_growth` | Theorem 1's full maximal-product estimate |
| `canonical_uniform_bound` | Literal final quantifier order and every generator selection of the unchanged original problem |

`IsComplexNorm`, `IsUnitary`, `WordIn` and `LowerForWeights` contain only their
ordinary mathematical definitions. They do not contain the final growth bound.
The first two have mandatory existence obligations; `WordIn` has actual maximum
witnesses; and the damping predicate is consumed by a theorem precisely on
block-lower-triangular matrices. The final theorem assumes none of the rounded
coordinate data, segment estimates or comparison results.

## Deliberate changes from the manuscript

The constant uses 6 in place of `2 exp(1)`, justified by the future consumed
certificate `exp(1)≤3`. This is a permitted nonoptimal enlargement of a constant
whose value is not specified by the original question. Zero-based finite indices
and chronological lists replace the source's one-based matrix lists.

Intermediate existence and comparison theorems are specialized to radius one
to avoid formalizing auxiliary zero-radius and general-radius statements not
asked by MF-07. This does not narrow the final target, whose exact premise is
radius one. The d=1 case, infinite families, all positive lengths, reducible
families and all complex entries are retained.

The source's stronger Hölder result, general-radius formula, zero-radius
nilpotence, sharpness claim and real-field extension are not claimed as verified
results of this one-problem draft. None is needed to establish the complete
original MF-07 statement.
