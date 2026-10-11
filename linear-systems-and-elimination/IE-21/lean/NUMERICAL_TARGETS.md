# Joint IE-21 / IE-22 numerical and semantic targets

Status: proof development. The shared trimming and cutoff exports are proved;
the main unconditional asymptotic theorems are not. See DEVELOPMENT.md.

## Exact objects

- Scalars are real. `Vector n` is `EuclideanSpace ℝ (Fin n)` and `Rows m n`
  is the family of the m row vectors, equivalent to an m by n real matrix.
- `UnitRows A` means every row has Euclidean norm exactly one.
- `retainedCount θ m` is the natural floor of the real number θ*m.
  Main targets assume 0<θ<1 and positive m,n. Semantic lemmas also cover θ=0,1,
  m=0, empty retained sets, ties, and rank deficiency when their domains permit it.
- `retainedEnergy A S x` is the finite sum of squared real inner products.
  `trimmedEnergy` is the infimum over exactly k retained rows AND all unit x.
  `deletionSingularValue` independently uses the square root of each such sum.
  Proving attainment, nonnegativity, and the square bridge is required: no SVD
  convention or a replacement target is hidden in these definitions.
- `operatorNorm` is the norm of the associated continuous linear map between
  Euclidean spaces. It is not an entrywise or infinity norm.
- `sphericalLaw n` is the pushforward of normalized `volume.toSphere` on the
  unit sphere. `sphericalRowsLaw m n` is its finite product. The Gaussian
  representation must be proved equal to this specified surface law.
  The raw definition at n=0 is not a probability measure; every probability
  target assumes positive dimensions, and all admissible asymptotic sequences
  eventually have positive dimensions. No cross-joint independence in j is needed.
- `GaussianCutoff θ a` explicitly means a>0 and P(-a≤G≤a)=θ for a standard
  real Gaussian G of mean zero and variance ONE. Existence and uniqueness are
  included in the IE-21 challenge to prevent a conditional or vacuous conclusion.
- `gaussianTrimmedMoment a` is the Gaussian integral of t² on [-a,a], exactly
  the canonical density integral. This density/measure bridge is required.
- `extremalDeletion θ m n` is the supremum over all unit-row matrices of
  sqrt(n/m)*sθ(A). Nonemptiness and upper boundedness must be established.
- Convergence in probability is stated directly as convergence to zero of
  every positive-tolerance bad-event probability under the varying finite
  product measures. Arbitrary dependence between different sequence indices
  is allowed. The only growth assumptions are n→∞ and m/n→∞.

## Intended exports

IE-21: existence/uniqueness of Gaussian cutoff; squared variational bridge;
finite trimming duality; normalized trimming and operator-energy limits;
canonical ratio limit; explicit joint finite-dimensional error bound.

IE-22: universal upper bound for every m≥1 once n is large; the canonical
supremum upper bound with N,R quantifiers; a fixed positive-gap witness beyond
EVERY N,R for each c<sqrt(hθ); convergence of the supremum along every allowed
sequence. The two problems retain separate IDs and statement boundaries.

## Quantitative proof route

For IE-21 set L=2/(1-θ). With m≥1, n≥2, 0<t,δ<1 and η,ρ>0, the proposed error is
D=η+2ρ+L/m+2(1+t)δ+sqrt(2/n). The challenge bounds the probability of the union
of |(n/m)||A||²-1|>t and |(n/m)sθ(A)²-hθ|>D by

2*9^n*exp(-m*t²/512)
+ 2*(1+2/δ)^n*(L/ρ+2)*exp(-2*m*η²/L²).

This replaces the source quantile argument with a threshold grid of mesh ρ.
All inequalities are strict bad-event inequalities; floor error is at most L/m.
A corollary should bound the ratio error by (D+t)/(1-t), using 0≤hθ≤1.
The original random error order can be recovered with explicit parameter choices;
the source's exact failure constants are not claimed unchanged.

For IE-22 the accepted implementation plan replaces Gaussian Poincare by an
elementary Gaussian Lipschitz covariance estimate. The resulting squared error
is Oθ(n^(-1/12)), weaker than the manuscript's additional Oθ(n^(-1/6)) refinement.
This preserves the exact canonical limit and sharpness target. The stronger
source rate is not an advertised result of this initial implementation.

## Simplifications and proof obligations

1. Use finite subset minima and the hinge dual, without a sorting API.
2. Define population trimming by the threshold supremum and prove its Gaussian
   value directly. No general quantile or conditional-expectation selector theory.
3. Reuse bounded-variable Hoeffding from Mathlib. Use independent radius-direction
   coupling and Jensen for spherical-square MGF domination by Gaussian squares.
   These centered squares have a restricted MGF bound, NOT a global sub-Gaussian one.
4. Share scalar Gaussian moments, covariance identities, nets, threshold grids,
   Lipschitz extensions and spectral trace bounds across both problems.
5. Derive deterministic sharpness witnesses from positive-probability IE-21 events.
6. Prove measurability and nonempty/bounded extrema before using real-valued measure
   and conditional completeness lemmas; do not exploit totalized empty extrema.

## Source and trust

Mathematical resolution: Matthew J. Colbrook, joint IE-21-22 manuscript.
Original problem: Stefan Steinerberger, arXiv:2107.05554v1, section 2.3.
Canonical targets, full manuscript, review and development base are hashed in
`verification/source-lock.json` in the IE-21 project. The independent review is
an AI-agent mathematical review, not human peer review or Lean certification.

No numerical certificates or LeanCert computation are needed for these analytic
proofs. Challenge placeholders are deliberate and must never enter a solution
import closure. Final checks must allow only propext, Classical.choice and
Quot.sound and must include a fresh isolated Linux Comparator/kernel run.
