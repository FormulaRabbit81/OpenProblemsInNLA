# FR-05 theorem contract and current scope

## Full target (specified, not yet formalised)

For every natural number `d ≥ 2`, take an independently standard complex
Gaussian matrix `A : ℂ^((4d-5) × d)`, where each real and imaginary coordinate
has variance `1/2`. Let `p_d` be the probability that, for all signals `x,y`,
equality of the componentwise moduli of `A x` and `A y` implies
`y = exp(θ i) x` for some real `θ`. The source's Theorem 1.4 claims

```text
∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → p_d ≤ C / d.
```

This exact signature is recorded, deliberately unproved, in `Challenge.lean`.
The original FR-05 conclusion is `p_d → 0` as `d → ∞`.

## Current kernel-checked checkpoint

`NLA.FR05.explicit_noninjective_frame` proves, for every `d ≥ 2`,

```text
∃ A : Matrix (Fin (4*d-5)) (Fin d) ℂ,
  ¬ PhaseRetrievalInjective A.
```

Here `PhaseRetrievalInjective` is the original all-pairs statement, with actual
row-modulus measurements and the relation `y = exp(θ i) • x`. The explicit
frame is intentionally simple (all entries one); its witnesses are the first
two standard basis vectors. This establishes the deterministic exact-ambiguity
bridge used by the source, but it does **not** assert an open neighbourhood,
positive Gaussian probability, a planted law, an `L²` likelihood comparison,
or the claimed `C/d` bound.

`NLA.FR05.RankTwoSeed` additionally checks the finite identities

```text
Q₀ = diag(1,-1,0,...),   Q₀ = Q₀ᴴ,   1ᴴ Q₀ 1 = 0.
```

The last equality is the source's exact seed cancellation for a constant row.
It is not a proof that the flat frame has the locally regular, rank-two kernel
structure or probability behavior required by the manuscript.

## Kernel-checked quantitative assembly

`Probability.lean` defines the scaled real-Gaussian complex frame law and
proves `0 ≤ p_d ≤ 1`; until event measurability is proved, this is the outer
measure of the exact injectivity event. `MainReduction.lean` proves the
following conditional form without asymptotic notation:

```text
if D ≥ 1, a,b ≥ 0, and for every d ≥ D,
  p_d ≤ a/d² + sqrt(b p_d/d),
then ∃ C > 0, for every d ≥ 2, p_d ≤ C/d.
```

Thus the only quantitative analytic interface remaining at the final assembly
boundary is the displayed eventual comparison. It still has to be derived
from the planted-failure and likelihood-comparison estimates in the source.

## Source constants reserved for the later analytic development

- `N = 4d - 5`, `d ≥ 2`;
- `η = 1/100`, `δ = d⁻²`, `ε = d⁻⁵⁰`;
- the source's local correlation margin is
  `η(1-η)/10 - 4η² > 1/2000`;
- the planted small-singular-value threshold is `κ = d⁻¹²`.

These constants are documentary only in this checkpoint. They will become
quantified real inequalities in the later planted-law and correlation modules.
