# KE-05 complete negative target — statements-only draft

This draft has no proof implementation and no verification claim. Ten deliberate
Challenge placeholders exist solely to type-check the proposed boundary. A future
Solution must not import Challenge. Two independent statement approvals are
required before freezing these bytes or writing the proof.

The full canonical README and George Stepaniants's complete solution, Sections
1–5 and scope notes, were read at commit
`deb549fa9ddd6b119e6c59016f268237e645dfa2`. Exact source and authorship hashes are
in `SOURCE_PROVENANCE.json`. Nian Shao retains the original framework/conjecture
credit. The new formalization draft is Sidney Holden's AI-assisted work.

## Literal problem semantics

Data is an arbitrary family of real diagonal entries in b-by-b blocks, for every
b≥1,d≥2. `Admissible` requires pairwise disjoint spectra **between** blocks and
does not exclude repeated entries within a block, interlaced spectra, or small
gaps. Data is quantified outside the probability expression and cannot depend on
the Gaussian outcome.

The sample space contains all d*b*b real entries. `gaussianLaw` is the finite
product of Mathlib's actual `gaussianReal 0 1` measures, one for each entry. Thus
all entries are independent standard real Gaussians. No bounded box law, discrete
surrogate, conditional distribution or specially selected numerical outcome is
substituted for that law.

For each root k, the block order is the actual ascending list with k moved first.
`rootOrder` indexes that list. Its default value is unreachable at a valid Fin d
index; the first comparator contract additionally requires equality of the entire
indexed list to the prescribed order. The recurrence is evaluated by descending
finite fold over i and ascending finite fold over j. Each step computes
S := B_i*S−S*hatB_j and then computes hatOmega_i=Omega_i*S and
hatB_i=hatOmega_i⁻¹*Lambda_i*hatOmega_i. The exported recurrence contract requires
the final arrays to satisfy those literal formulas. No commutative reordered
product or imported matrix-polynomial factorization theorem defines the process.

`spectralNorm` explicitly uses the continuous linear map on Euclidean spaces,
not an accidental entrywise or infinity matrix norm. Both endpoints are the
actual extrema of all diagonal entries. The ordering-specific monomial constant
includes 1 and both endpoint ratios for every nonfirst block. A ratio is set to
1 exactly in the stated 0/0 case. The coefficient constant uses the actual inverse
of S_(first,last), the exponent 1/(d−1), and the minimum cross-gap between the root
block and every other block. Global mono and coef are separate maxima across all
root orderings; they are multiplied only afterward.

Matrix inverse is total in Lean. `Valid` explicitly requires all initial Gaussian
matrices and every transformed Omega to have nonzero determinant. These are all
inverses required by the recurrence; the coefficient inverse is then valid as
well because the original Omega and its product with S are invertible. On invalid
outcomes only, `totalConstant` is assigned zero. A comparator theorem requires
validity almost surely for **every** admissible data family and measurability of
the actual total constant. Consequently totalization changes no probability in
the canonical question and cannot be used to bypass singularity obligations.

`UniformProbabilityConjecture` retains the full quantifiers: for every b,d and
0<delta<1 there exists a finite real C such that every fixed admissible input has
probability at least 1−delta of totalConstant≤C. The real probability is the
toReal of the actual product-Gaussian event measure, which is a probability
measure. There is no simultaneous-all-inputs good-event requirement.

## Numerical and algebraic targets

Use b=2,d=3 and Lambda=(2I,diag(e,2e),diag(0,1)), with 0<e<1/4. Prove
admissibility, actual endpoints a=0,c=2, and first-root cross-gap=1. This entire
deterministic parameter interval is retained.

With X=Omega_2⁻¹ diag(1,2) Omega_2 and P=Omega_3⁻¹ diag(0,1) Omega_3, set
kappa=tr((I−P)X), Q=(I−P)XP, and N=−Q/kappa. The fixed rational sample
Omega_1=Omega_2=I, Omega_3=[[1,2],[3,5]] must give
X=diag(1,2), P=[[6,10],[-3,-5]], kappa=7, Q=[[30,50],[-18,-30]], and
the actual spectral norm ||N||=68/7. This witness is used only to show relevant
numerator polynomials are nonzero. Its Gaussian probability is zero; it is never
treated as a positive-probability counterexample event.

Planned exact reduction: det(eX−P)=e(2e−kappa) and the 2-by-2 adjugate identity
cancel e before any limiting calculation. The resulting transformed second block
tends to N when kappa≠0. Prove kappa≠0 and Q00≠0 almost surely under the original
Gaussian law, not as hypotheses on the sampled outcomes.

The coefficient determinant in root order zero is
2(2−e)(2−2e), lying strictly between 0 and 8. The intended norm proof therefore
yields coef≥8^(−1/4). Together with mono≥||hatB_2||/(2e), the exported lower-bound
theorem compares this exact product with the **literal full global constant**.
No numeric rounding, broad matrix interval enumeration or oracle norm evaluation
is needed; any LeanCert numeric certificate must feed this exact proof chain.

## Probability bridge and final conclusion

Use epsilon(m)=1/(m+6) for natural m≥0, exactly the manuscript sequence indexed
there by m≥1 after a shift of one. The same Gaussian sample at each m is only a
coupling device; each marginal remains exactly the original law.

Prove a single probability-one event on which every ordering is valid for every
m, kappa and Q00 are nonzero, and the actual transformed second blocks converge
to the nonzero N. Then prove the literal total constants tend to +infinity almost
surely. For **every finite real C**, require the actual marginal probabilities
of totalConstant≤C to tend to zero. Deduce an admissible deterministic input with
probability below 1/2 for each C and negate the full conjecture at delta=1/2.

## Reuse and review status

Inspected pinned Mathlib Gaussian/Real and Gaussian/Multivariate for the actual
normal density and product law, Analysis/CStarAlgebra/Matrix for the Euclidean
operator norm, and existing RA-07 statement definitions for retaining literal
canonical expressions rather than numerical replacements. No NLA theorem is
assumed. The computational reduction is exact 2-by-2 adjugate algebra. The
polynomial-null-set and probability-limit arguments remain genuine obligations;
checking the rational witness alone cannot establish them.

The intended comparator exports are all ten declarations in Challenge, with no
definition-name substitutions and only the usual three permitted logical axioms.
Type-checking establishes well-formedness only. This draft has no Solution, no
completed LeanCert trust audit, no Linux Comparator run and no final-proof reviews.
