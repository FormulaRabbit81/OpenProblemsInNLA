# Joint IE-21 / IE-22 development

Both formalizations are **incomplete**. The canonical problem pages and statuses
are unchanged. Proof development proceeded at the user's request before
independent statement review. All results use ordinary theorem statements.

## Proved and locally checked

Three complete IE-21 challenge exports are implemented with their stated types:
`gaussianCutoff_existsUnique`, `deletionSingularValue_sq`, and
`finite_trimming_duality`.

The shared `NLA.RowDeletion` library also proves:

- finite trimming certificates, including ties, empty selections and full retention;
- a bounded threshold certificate using only the total sum, and threshold Lipschitz bounds;
- population trimming stability under a coupling and identification at a cutoff;
- existence and uniqueness of the Gaussian cutoff, the density-integral bridge,
  and the bounds zero <= h <= one;
- real Gaussian projection laws and moments, the exact Gaussian-square exponential
  integral, and the bound E exp(t(G²-1)) <= exp(32t²) for t <= 1/8;
- Jensen's exponential comparison for an independent mean-one multiplier;
- probability normalization and unit-row support of the specified spherical law;
- a radial-density polar-coordinate theorem, identification of normalized Gaussian
  direction with that surface law, and independence from the Gaussian radius;
- reconstruction of a Gaussian from an independent spherical direction and radius,
  the scalar projection law for this product coupling, and the row-wise law bridge;
- Gaussian radius moments E R² = n, E R⁴ = n(n+2), and Var(R²) = 2n;
  for D = R²/n, E D = 1, Var(D) = 2/n, and E |D-1| <= sqrt(2/n);
- spherical projection integrability and isotropy E n<b,U>² = ||b||²;
- the exact Gaussian coupling-error factorization, its ||b||² sqrt(2/n) bound,
  and the population-trimming comparison with h_theta for every unit direction;
- transport of population trimming through any measurable map, with no continuity
  or quantile assumption on the random variable;
- a threshold grid of cardinality at most L/rho+1, two-sided bounded-average
  concentration from Mathlib's Hoeffding theorem, and the grid union bound;
- nonnegativity and boundedness of the variational quantities and actual supremum;
- deterministic witness extraction and the ratio-limit implication on varying spaces.

IE-22 imports this library through its Lake dependency. Its `IE22.Transfer`
module proves the supremum upper-bound implication, sharpness from concentration
only along m=n², and extremal convergence from concentration plus a uniform upper
bound. **These are implications with explicit, still-unproved analytic hypotheses,
not the unconditional IE-22 challenge exports.**

## Proof simplifications already implemented

1. A minimum subset and an exchange argument replace sorting and order statistics.
2. Continuity of square root on infima replaces an SVD or interchange of attained minima.
3. The hinge supremum gives the coupling bound directly, without conditional selectors.
4. Outside the total-sum cutoff the threshold objective is nonpositive; zero is a
   competing threshold. No count of observations below the cutoff is needed.
5. A Gaussian integral, Jensen and a scalar logarithm inequality replace moment series.
6. Sharpness uses just m=n². The general extremal limit reuses the same witness lemma.
7. Mathlib's Haar-to-sphere theorem factors a radial density. The actual radius
   marginal supplies its normalization, avoiding a Gamma integral or explicit
   sphere-area formula. This proves the bridge for every radial probability
   density, with the Gaussian case as a direct application.
8. The scalar fourth moment follows by differentiating the already-proved
   Gaussian-square exponential integral. Independence adds the coordinate
   variances, and nonnegativity of variance gives the radius L¹/L² bound.
   No separate chi-square distribution or radial moment integral is needed.
9. The Gaussian vector itself realizes the spherical/Gaussian coupling. Independence
   and E(R²/n) = 1 give spherical isotropy from the existing Gaussian second moment.
   Factoring the absolute error leaves exactly the radial L¹ deviation. Transport
   of hinge integrals then applies the existing population-trimming stability bound,
   including in dimension one where the spherical projection law has atoms.

## Remaining main proof work

1. Transfer the Gaussian exponential estimate to spherical projections, then combine
   scalar concentration with sphere nets and directional quadratic-form bounds to
   establish IE-21's joint bound and its two basic asymptotic limits.
   The ratio transfer is already proved.
2. Establish IE-22's spectral projection and correlated Gaussian variance estimates,
   then its unconditional uniform upper bound. The elementary covariance route
   proposed in NUMERICAL_TARGETS.md has not yet been proved in Lean.
3. Discharge the explicit hypotheses in the transfer modules and export all
   unconditional main theorems.

## Reproduction and review boundary

Lean 4.33.1; mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Both lake-manifest.json files record the transitive package revisions.
For local development, ignored .lake/packages symlinks reuse the existing cache.
No imported mathematical source is changed by this setup.

From either project directory:

```sh
lake build
lake env lean verification/CheckAxioms.lean
```

The default builds contain only proved implementation modules. The axiom audit
checks every imported declaration in the NLA namespace and fails on anything
beyond `propext`, `Classical.choice`, and `Quot.sound`.
`lake build Challenge` separately checks the target signatures; its deliberate
`sorry` placeholders are never imported into the implementation.
IE-22 uses the distinct module root `IE22` to avoid Lean module-search collisions
with the shared dependency's `NLA` root and its challenge module. Its theorem
namespace remains `NLA.IE22`.

`verification/source-lock.json` records the original mathematical sources.
`verification/statement-candidate.json` is the historical initial candidate,
not an approval or a current hash of the evolving documentation.
`verification/proof-development.json` records the current development snapshot.

Full Comparator verification has not been run: unconditional exports are
missing. Before publication, IE-22 needs an immutable Git/subDir dependency;
independent review and fresh non-root Linux Comparator/kernel checking remain
outstanding. No completion metadata or repository safeguards have been relaxed.

The mathematical source is the recovered joint IE-21/IE-22 manuscript. The threshold-grid,
Jensen-MGF and elementary Gaussian-covariance substitutions are documented in
NUMERICAL_TARGETS.md. The planned Gaussian-covariance route targets a weaker
additional finite-n rate for IE-22 while retaining its exact canonical target.

## Integration with the published scaffold

The draft PR is based on fork main at `775bedc1e33cc0951d08610cc7ba50d2901eda1a`.
Each project retains the prior scaffold verbatim under
`verification/published-scaffold`, with an immutable hash manifest. Historical
review approval is not applied to the current candidate. The current root
README and metadata describe the new partial proof scope. Original source
hashes remain tied to the development base; `pr_base_sha256` separately records
the newer fork base, whose canonical pages add only scaffold links.
