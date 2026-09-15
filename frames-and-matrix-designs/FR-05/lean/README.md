# FR-05 Lean development

This project begins the formalisation of the claimed (O(d^{-1})) phase
retrieval result, using the frozen [source manuscript](sources/README.md).
It is deliberately an **incomplete checkpoint**, not a Lean
verification of FR-05 and not evidence for changing the catalog status.

The checked exports are `NLA.FR05.explicit_noninjective_frame` and
`NLA.FR05.likelihood_l2_bound_of_second_moment_estimates`. For every
dimension `d ≥ 2`, the first builds a `4d-5` row complex frame whose actual
entrywise-modulus phase-retrieval map is noninjective. The public definitions
retain all signals and the original relation `y = exp(θ i) • x`; the proof
constructs the two standard-basis witnesses directly. Supporting lemmas also
check that Li's diagonal seed `Q₀ = diag(1,-1,0,...)` is Hermitian and that
its quadratic form vanishes on the constant-one row.

`Probability.lean` defines the iid complex-Gaussian frame law by scaling a
real multivariate Gaussian, proves its coordinate map measurable and its
total mass one, and records the nonnegativity and upper bound of the resulting
outer measure. `MainReduction.lean` proves the final algebraic assembly: an
explicit eventual inequality of Li's displayed Cauchy--Schwarz form implies
the claimed inverse bound. That eventual inequality is a hypothesis of the
checked lemma, not an assumed result.

`LikelihoodAlgebra.lean` checks the exact algebraic end of Proposition 3.2:
given integrability and two eventual $C/M$ second-moment estimates for
$L_g^2-L_r^2$ and $L_gL_r-L_r^2$, it derives the eventual L² estimate
$\int (L_g-L_r)^2 \le 3C/M$. This is a generic conditional reduction; it does
not define Li's likelihoods or establish those hypotheses from the source.

This formalises the exact-ambiguity bridge, the last numerical reduction, and
the final algebraic transition in the source's Proposition 3.2. It does
**not** prove measurability of the injectivity event, the local rank-two chart,
quantitative contraction, Haar/Stiefel measure, small-ball estimates, overlap
density, the source-specific likelihood comparison, or its eventual
second-moment estimates. Consequently, it does **not** prove either the full
source Proposition 3.2 or the unconditional `p_d ≤ C/d` theorem. Those
dependencies are mapped in the parent
[formalisation plan](../formalisation-plan.md) and in
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md).

## Development checks

The project pins Lean 4.33.1 and Mathlib in `lakefile.toml`. Once dependencies
are present, run:

```sh
lake build
lake build Challenge
lake env lean Solution.lean
```

The three `Challenge.lean` placeholders are development-only statement
comparison fixtures and are never imported by `Solution`. No Comparator run,
independent statement review, Linux sandbox verification, or formalisation
claim for the full FR-05 result is made at this stage.
