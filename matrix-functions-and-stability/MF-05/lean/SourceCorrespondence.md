# MF-05 original target and exact contract correspondence

This is a statement-author mapping, not an independent approval or proof. The exact current canonical README and original 299-line manuscript were read from local published Git object `5308b2cfa30826e1314d6a8830415c14b5f1d7a3`. Both are byte-identical to upstream `849003686970b372e1b2128ba072f86168f81d38`. The canonical copy is `sources/canonical/README.md`. `sources/reuse/MF07-PUBLISHED-BINDINGS.json` and `sources/reuse/SOURCE-CAPTURE-RECEIPT.json` bind the actual read-only retrieval, original manuscript hash and exact published MF07 code. The manuscript is Matthew J. Colbrook's *Uniform polynomial product bounds and sharp Hölder continuity of the joint spectral radius*, Theorem 2, Proposition 5, Corollary 7 and the proof of Theorem 2. The original manuscript contact preamble remains in the separate private source-evidence snapshot, not in this prospective proof project.

## Objects and quantifiers

| Canonical object | Concrete declaration and semantics |
|---|---|
| Complex d-by-d matrices, every d>=1 | Published `NLA.MF07.Square d = Matrix (Fin d) (Fin d) ℂ`; the target has explicit `hd : 1 ≤ d`. |
| Arbitrary nonempty compact matrix families | Unrestricted `Set (Square d)`, with explicit `IsCompact` and `Nonempty` hypotheses. There is no finite-generator, irreducible, real-only, normalized-radius or invertibility requirement. Matrix compactness uses the usual finite-dimensional topology. |
| Spectral norm | Published `spectralNorm A = ‖Matrix.toEuclideanCLM A‖` on complex Euclidean space. No default entrywise matrix norm is used for distances or products. |
| Every product A_n ... A_1 | Published reversed-list `matrixProduct`, unrestricted `WordIn`, and `familyGrowth` over all words of the specified length. Existing `family_growth_maximum`/`familyGrowth_attained` prove the actual compact maximum; empty words are included in the supporting estimates. |
| Original nth-root limit | Published `rootGrowth`, and `jointSpectralRadius` as the infimum of positive-index roots. New mandatory `general_root_limit_semantics` proves the full original limit for every eligible family, including zero radius. Published radius-one semantics is insufficient for this purpose. |
| Literal spectral Hausdorff formula | New `pointFamilyDistance`, `directedSpectralDistance` and `canonicalHausdorff` are exactly the canonical infimum, supremum and maximum. |
| Library Hausdorff distance | New `spectralImage` applies the actual matrix-to-Euclidean-operator map, and `spectralHausdorff` uses `Metric.hausdorffDist` on those images. The mandatory correspondence theorem proves compact images, finite Hausdorff edistance, the original formula, zero iff set equality and attained nearest generators in both directions. |
| Local two-family quantifier order | `canonical_local_holder` fixes d and M0, then chooses positive r and C, then quantifies independently over M and N. The same constants bound every pair in that neighborhood. |
| Exponent and constant | `Real.rpow` with exponent `1 / (d : ℝ)`; intermediate uniform constant is exactly `d*(2*d+1)*L^(1-1/d)`. Positive bases and all corner cases are explicit in the supporting contracts. |

## All 14 independent obligations

The exact headers and source lines are in `CONTRACT-MAP.json`; all are intentional Challenge holes. No header is an implementation or a proof assumption hidden in a definition.

| Declaration in NLA.MF05 | Source/role and intended consumers |
|---|---|
| `half_radius_certificate` | New fixed rational certificate `0 < localRadius < 1`. Future kernel LeanCert proof must be consumed by `local_common_norm_ball` and the positive radius choice in `canonical_local_holder`. |
| `spectral_hausdorff_semantics` | Canonical Context and notation, first displayed formula. New bridge to the existing Mathlib Hausdorff API, consumed by perturbation, zero-distance and final literal-metric transport. |
| `general_exponential_envelope` | The finite exponential boundedness used in manuscript Lemma 3 and Corollary 7. New general finite-block proof over the actual radius infimum; supplies the root limit and identity-adjunction bounds. |
| `general_root_limit_semantics` | Canonical Context and notation, second displayed formula. Bounds radius in `[0,familyNorm M]` and proves full nth-root convergence, with no radius-one/positivity premise. Mandatory package semantics even though the final theorem names the reused infimum definition. |
| `positive_scaling_semantics` | Homogeneity needed to consume the published normalized comparison. Actual scalar generator images, compactness/nonemptiness, exact family norm, every word-growth value and actual radius. |
| `exponential_bound_controls_radius` | Converts a proved positive-rate exponential word bound into an inequality on the actual radius. Used in identity-adjunction and perturbation; not an unproved abstract operator-norm spectral-radius oracle. |
| `scalar_identity_adjoin_radius` | Explicit new bridge: adjoining eI gives radius `max(rho,e)` and family norm `max(familyNorm,e)`. This is a conclusion for every e>0, including rho=0, not a hypothesis. |
| `general_quantitative_comparison` | Manuscript Proposition 5, every n>=0 and s>=1: `a_n ≤ d*s^(d-1)*(rho+2*d^2*L/s)^n`. Reuses the exact published radius-one theorem via scaling and identity adjunction. |
| `controlled_comparison_norm` | Corollary 7's specified discounted-word norm, instantiated as the actual published `productEnvelope`. Its positivity, four complex norm axioms, Euclidean bounds and generator estimate are conclusions; no extremal-norm existence structure is assumed. |
| `hausdorff_radius_transfer` | One-sided step in the proof of Theorem 2. Only the source family M needs the supplied L-ball; N is any nonempty compact family. Nearest generators and the proved norm bounds give the quantitative radius transfer. |
| `holder_scale_identity` | Theorem 2's symbolic choice `s=(L/delta)^(1/d)` for 0<delta<=L, including d=1. Gives s>=1, the exact d-th power, the L/s identity and the optimized coefficient. |
| `uniform_holder_estimate` | Complete Theorem 2 estimate for two families in one common positive L-ball, including delta=0, delta>=L and either radius zero. Also proves its displayed constant is positive. |
| `local_common_norm_ball` | Canonical local-neighborhood reduction. The certified half-radius neighborhood of M0 lies in `familyNorm M0+1`, a proved positive bound. Apply to each varying family. |
| `canonical_local_holder` | The exact complete original Problem statement, with the literal `canonicalHausdorff` metric. Witnesses may be `r=1/2` and `C=holderConstant d (familyNorm M0+1)`; no witness is assumed. |

## Zero-radius bridge and absence of circularity

The published MF07 comparison assumes radius one. This draft does not rename that theorem into an arbitrary-radius result. First obtain a finite-block exponential envelope directly from the actual infimum: choose k>=1 with root growth below a, write n=q*k+r, use submultiplicativity and the finite set of remainders. A positive discount allows division only by a^r; no logarithm of a zero growth value is taken. The resulting envelopes give the full root limit and the radius transfer for any exponential bound.

Positive scaling can then be proved on actual words and limits. For an adjoined scalar identity, each word equals a scalar power times an order-preserving compressed word in M. This is an equality for each word, so there is no binomial multiplicity factor. A bound with any rate larger than max(rho,e) gives the upper radius bound; old words and the all-identity word give the lower bounds. No continuity of the radius is used.

For rho>0, normalize by rho, consume the exact published quantitative comparison and scale back. For rho=0, adjoin eI with 0<e<=L, use the proved max formula and the same positive-radius argument, and let e decrease to zero in the scalar polynomial bound for each fixed word length. Only scalar continuity is used; continuity of the joint spectral radius is the desired conclusion and is never a premise.

The new `comparisonNorm` is the explicit published discounted-word envelope at the proved positive rate. Its bounds imply a genuine complex norm and control perturbation action. Iterate generator inequalities over each actual word, convert to a Euclidean operator-norm bound using the two proved norm comparisons, then invoke the proved exponential radius bound. This supplies the one-sided estimate without assuming an abstract radius inequality. The symbolic root choice optimizes it; zero-distance equality and the elementary `[0,L]` bound cover the remaining distance cases.

No mathematical gap was identified in this statement-author feasibility check. The general root, scaling, identity-word compression and Hausdorff bridges remain substantial unproved obligations, and syntactic elaboration is unrun. Two nonauthor reviews must assess the concrete source before any MF05 proof implementation.

## Scope retained

Dimension one is included with the displayed nonoptimal constant 3; the source's sharper scalar constant 1 is not required by the original existential target. The full target is over complex matrices; real-entry families occur inside that universe. The manuscript's bounded noncompact extension, sharpness examples, MF07 uniform-growth theorem as a distinct target and the separate MF06 lower-bound question are not additional MF05 completion claims. No count is advanced.

Credit Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, for the original mathematical proof, and George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for formalization. Reused code credits are unchanged. Substantial AI assistance is disclosed; no external human review or official Tau Ceti approval is claimed.
