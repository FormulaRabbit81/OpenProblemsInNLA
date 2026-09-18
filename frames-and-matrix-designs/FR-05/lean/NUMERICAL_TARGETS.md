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
positive Gaussian probability for the good event, a source-specific `L²`
likelihood comparison, or the claimed `C/d` bound.

`NLA.FR05.RankTwoSeed` additionally checks the finite identities

```text
Q₀ = diag(1,-1,0,...),   Q₀ = Q₀ᴴ,   1ᴴ Q₀ 1 = 0.
```

The last equality is the source's exact seed cancellation for a constant row.
It is not a proof that the flat frame has the locally regular, rank-two kernel
structure or probability behavior required by the manuscript.

## Checked Proposition 3.1 components

The current development also formalizes several source-specific components of
the planted argument:

- the conditioned radial mixture (3.2), the independent scalar/Gaussian
  coordinates in (3.18), and the exact iid planted-frame law;
- an equality representing that law as the pushforward of the checked
  `PlantedRow` construction;
- the exact source Jacobian row expression (3.21) at zero imbalance and its
  Gaussian variance profile;
- the initial-residual estimate `‖F^ε(0)‖₂ ≤ ε√N`, a source-scale radial tail
  `P(S ≥ 8M) ≤ 25 exp(-4M)`, and a complex-Gaussian tail estimate;
- the fixed-point implication from a verified contraction certificate to an
  exact noninjectivity witness.

The unproved central bridge is still the quantitative good-event probability:
the full phase small-ball estimate in Lemma 3.6, Lemma 3.7's least-singular
tail, and the derivative perturbation/Lipschitz estimates that make the
contraction certificate hold with high probability. Hence this is not yet a
formal proof of Proposition 3.1.

## Checked conditional L² step of Proposition 3.2

`LikelihoodAlgebra.lean` proves the source's final algebraic transition in
an explicit family-level form. For every $M \ge D$, assume the three product
integrands are integrable and

```math
\left|\int L_g^2\,d\mu_M-\int L_r^2\,d\mu_M\right| \le C/M,
\qquad
\left|\int L_gL_r\,d\mu_M-\int L_r^2\,d\mu_M\right| \le C/M.
```

It then proves

```math
\int (L_g-L_r)^2\,d\mu_M \le 3C/M.
```

This is the exact expansion-and-triangle-inequality end of Proposition 3.2,
after the source has established its pairwise moment estimates. It does not
define the planted/reference likelihoods, prove equation (3.17), construct
the Haar two-frame overlap law, or establish Lemmas 3.3--3.5 and the
local/tail bounds. It is therefore not a proof of source Proposition 3.2.

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

## Source constants used by the planted development

- `N = 4d - 5`, `d ≥ 2`;
- `η = 1/100`, `δ = d⁻²`, `ε = d⁻⁵⁰`;
- the source's local correlation margin is
  `η(1-η)/10 - 4η² > 1/2000`;
- the planted small-singular-value threshold is `κ = d⁻¹²`.

The definitions of `N`, `η`, `δ`, `ε`, and `κ` are already present in
`SourceParameters.lean`. The remaining displayed margins and all big-O
statements still require quantified constants and thresholds before they can
cross a theorem boundary.
