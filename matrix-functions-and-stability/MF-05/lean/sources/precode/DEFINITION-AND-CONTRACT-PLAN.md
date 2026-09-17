# MF-05 definition and contract plan

Draft planning only. This file precedes the new Lean definitions and Challenge. The root accepted the source-bound feasibility route; two independent reviews of the actual definitions/statements, actual local elaboration and the subsequent freeze remain pending. No MF-05 proof may be implemented before that gate.

The complete original target is the local two-family Holder estimate in every positive dimension for arbitrary nonempty compact subsets of complex matrices, using the spectral norm. Infinitely many generators, zero joint spectral radius, reducible families and distance zero remain included.

Reuse the exact 20 published MF-07 modules at upstream `849003686970b372e1b2128ba072f86168f81d38`, preserving their namespace and authorship. New declarations live in `NLA.MF05`; do not add compatibility aliases for MF-07 declarations. Use its actual Square, EuclideanVector, spectralNorm, matrixProduct, WordIn, familyNorm, familyGrowth, rootGrowth, jointSpectralRadius, IsComplexNorm and productEnvelope.

New concrete definitions:

- `spectralImage M`: the image under the actual complex Euclidean continuous-linear operator associated to each matrix.
- `pointFamilyDistance A N`: the infimum of all actual spectral norms of A-B for B in N.
- `directedSpectralDistance M N`: the supremum of pointFamilyDistance over A in M.
- `canonicalHausdorff M N`: the maximum of the two directed distances, exactly as printed in the canonical README.
- `spectralHausdorff M N`: Mathlib's Hausdorff distance of the two operator images. A mandatory contract equates it to canonicalHausdorff and proves nearest generators and distance-zero equality.
- `scaledFamily c M` and `identityAdjoin e M`: positive scalar images and insertion of the actual scalar identity matrix. They carry no radius assumptions by definition.
- `InNormBall M L`: every actual generator has spectral norm at most L.
- `comparisonFactor d s = d*s^(d-1)` and `comparisonRate d M L s = jointSpectralRadius M + 2*d^2*L/s`.
- `comparisonNorm d M L s`: the published actual productEnvelope of the identity generator map, discounted by comparisonRate. Its norm axioms/bounds are proved, not bundled as an assumed structure.
- `holderScale d L delta = (L/delta)^(1/d)` and `holderConstant d L = d*(2*d+1)*L^(1-1/d)`, with real powers and explicit natural-to-real coercions.
- `localRadius = 1/2` and `localNormBound M0 = familyNorm M0 + 1`.

Proposed independent Comparator contracts, in dependency order:

1. `half_radius_certificate`: 0 < localRadius < 1, via kernel LeanCert, actually consumed by the neighborhood bound and final radius positivity.
2. `spectral_hausdorff_semantics`: full canonical formula, nonnegativity, zero iff set equality, and nearest-point bounds in both directions for the actual spectral norm.
3. `general_exponential_envelope`: for every rate a greater than the actual infimum radius, a K>=1 bounds every word length by K*a^n, including zero growth.
4. `general_root_limit_semantics`: actual roots converge to the infimum radius, which lies between zero and the actual family norm.
5. `positive_scaling_semantics`: compactness/nonemptiness and exact family norm, every growth value and radius under any positive scalar image.
6. `exponential_bound_controls_radius`: every proved positive-rate exponential word bound controls the actual radius.
7. `scalar_identity_adjoin_radius`: compactness/nonemptiness and the exact max(radius,e) formula for every e>0.
8. `general_quantitative_comparison`: the full rho+2*d^2*L/s growth estimate for all s>=1 and all word lengths, with no normalization hypothesis.
9. `controlled_comparison_norm`: the actual discounted norm has all four complex norm axioms, lower/upper Euclidean bounds and the actual generator inequality.
10. `hausdorff_radius_transfer`: the one-sided radius perturbation inequality. Only the source family needs the L norm bound; the other compact family need not satisfy that bound for this one-sided lemma.
11. `holder_scale_identity`: s>=1 and the exact optimized scalar identity for L>0 and 0<delta<=L. Dimensions and powers remain symbolic.
12. `uniform_holder_estimate`: the full two-family estimate with the displayed dimension/L constant for two families in one common norm ball.
13. `local_common_norm_ball`: the half-radius neighborhood of arbitrary M0 lies in its explicit positive localNormBound ball.
14. `canonical_local_holder`: the exact original existential local two-family result. The root-limit and Hausdorff semantics contracts are mandatory parts of the same package.

The proof plan for arbitrary/zero radius is finite-block envelopes, positive scaling and scalar-identity adjunction. This allows the exact published radius-one `NLA.MF07.quantitative_comparison` to be consumed unchanged. No joint-spectral-radius continuity is assumed. Auerbach/SVD/triangular damping are reused, not rederived. No numerical matrix enumeration, word-length cutoff, sampled family, finite-generator restriction or interval subdivision is permitted to substitute for these quantifiers.

Each intended proof module will copy only its exact frozen theorem header; helpers are separate and use located Mathlib/MF-07 APIs. Definitions and independent Challenge remain immutable after the two reviews and actual elaboration/freeze. The eventual Solution must not import Challenge. Until then only intentional Challenge holes exist; no Solution or MF-05 proof implementation is created.
