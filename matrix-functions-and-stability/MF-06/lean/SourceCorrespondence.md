# MF-06 exact statement correspondence

This is an **uncompiled, unreviewed statement draft**, not a formal proof.
The source is the unchanged canonical README and complete solution at upstream
`3923b68ecee13d02e732085a57b42a2e7e95ac7a`, copied into `source-inputs/canonical/`.
The sealed pre-code audit remains unchanged in `../precode`; its manifest is
`993b09ca972bd6909e62fc19ae9690d4ddcfd03ed8b796aea3a353be3b0d08a7`.

The final C38 has the exact order

    for every d>=1 and fixed nonempty compact M,
      there exist r>0 and C>0,
        for every nonempty compact N,
          canonicalHausdorff(M,N)<r implies rho(M)-C*canonicalHausdorff(M,N)<=rho(N).

It does not require M or N to be finite, irreducible, product bounded, invertible,
or positive-radius. N need not preserve any subspace of M. The radius is the
actual all-word radius and the distance is the original max-of-two-sup-inf
formula in the spectral operator norm. C02 and C03 reproduce their complete
existing correspondence results, including all arbitrary-radius cases.

## Concrete meanings and library reuse

`NLA.MF07.Square`, `EuclideanVector`, `spectralNorm`, `applyMatrix`, chronological
`matrixProduct`, `WordIn`, `familyGrowth`, `rootGrowth` and `jointSpectralRadius`
are imported unchanged. `NLA.MF05` supplies the literal Hausdorff formula,
operator-image Hausdorff distance, actual positive scalar image and norm-ball
predicate. Their definitions and prior proofs are not reimplemented.
Exact source-bound reuse is pinned to published MF05 proof commit
`06b8cf49740205c4b7b0b71ee5c636855fbe26a6`, independently audited at its original
Linux run and later unchanged publication/PR checkouts. The eleven reusable
modules copied as `.lean.txt` are inert source evidence here. The root compiler
owner must use those exact source hashes when assembling a local typecheck.

The new all-word envelope is the existing `productEnvelope` at identity map and
rate one. `tailEnvelope` is a literal supremum over length-n original words;
`stableGauge` is its literal real infimum. C06 constructs an existing Mathlib
`Seminorm`, rather than introducing a parallel seminorm API or assuming its laws.
The actual kernel is characterized by membership iff that gauge equals zero.
`restrictedGrowth` is the supremum of actual Euclidean actions on unit vectors
in the submodule, with zero inserted so the bottom submodule is correctly covered.
`IsProductBounded` is used on nonempty compact families throughout the radius
arguments; total real suprema of unbounded or empty sets are never used as a
substitute for genuine word bounds.

Block labels partition the actual coordinates into fibers. Diagonal blocks are
the corresponding literal submatrices. Surjectivity in the block/flag contracts
ensures positive block dimensions. The flag theorem supplies actual inverse
matrices and an actual upper-block-triangular family. It does not accept a
preconstructed flag containing an assumed conclusion.

The compound matrix contains the sorted minors indexed by
`Set.powersetCard (Fin d) k`, reindexed by `Fintype.equivFin` into `Square`.
C18 identifies that explicit map with Mathlib's algebraic `exteriorPower.map`
in `Module.Basis.exteriorPower (Pi.basisFun ...)`. C17 proves the basis cardinality
is `Nat.choose d k`; C19 proves multiplicativity and the degree-zero identity.
Thus a determinant of the entire matrix or an abstract function satisfying
assumed bounds cannot replace the full exterior family.

`tensorMatrix` reindexes the actual library `Matrix.kronecker` through
`finProdFinEquiv`. The allocation matrix is the actual finite product of the
entries of each diagonal block's compound matrix. All factors use the **same
original A**. Allocations have indices `Fin(d_i+1)`, retain degree-zero factors,
and keep all empty words and vanishing minors. Pointwise maximum/minimum of
allocations stay within those real block dimensions.

## Complete contract map

The source line locators below refer to `source-inputs/canonical/solution.md`.
All C05–C38 are obligations to prove, not results obtained by this draft.

| ID | Declaration suffix | Source correspondence / required content |
|---|---|---|
| C01 | MF05.half_radius_certificate | Existing kernel-mode LeanCert certificate; exact reuse and genuine consumption planned in C09/C10/C37. |
| C02 | MF05.spectral_hausdorff_semantics | README literal Hausdorff formula; both nearest-generator directions, zero-distance equality, compact images and finiteness. |
| C03 | MF05.general_root_limit_semantics | README root limit, solution §1–2; all actual word maxima and arbitrary-radius root semantics reused. |
| C04 | MF05.positive_scaling_semantics | Solution §1 and §6 normalization, including word-length growth and actual image radius. |
| C05 | bounded_envelope_norm | Lemma1 lines45–47; actual undiscounted envelope and its genuine complex norm/action bounds. |
| C06 | tail_seminorm_limit | Lemma1 lines47–55; decreasing tail suprema, compact-uniform convergence and continuous Mathlib seminorm equal to the concrete infimum. |
| C07 | stable_gauge_max_recurrence | Lemma1 lines53–56; actual compact attainment of the limiting maximum recurrence. |
| C08 | stable_kernel_exponential | Lemma1 lines57–63; actual kernel, proper invariant submodule, strict uniform exponential decay, including S=bottom. |
| C09 | cone_numerical_bound | Lemma1 lines65–85; symbolic cone constants, invariant-cone inequality and positive half growth factor. |
| C10 | product_bounded_lower_lipschitz | Entire Lemma1 lines43–89; prove the quotient norm, stable-block norm, real perturbing lower-left block and all-length trajectories internally, without periodic-attainment assumptions. |
| C11 | separated_sum_bound | Lemma2 lines93–113; all lengths and all 0<q<1. A larger explicit finite constant eliminates a square-root computation. |
| C12 | block_radius_formula | §2 lines28–39; complete finite-block triangular family radius, preserving the common original word. |
| C13 | block_nonresonance_product_bounded | Lemmas3–4 lines115–171; complete paired-tensor two-block estimate and finite-block induction. Adjacent empty gaps and grouped-prefix off-diagonal terms cannot be dropped. |
| C14 | irreducible_radius_one_product_bounded | §5 lines175–182; prove the needed extremal-norm consequence, rather than adding a literature axiom or an extremal-norm hypothesis. |
| C15 | irreducible_flag | §5 lines175–182; actual finite irreducible invariant flag for every matrix family and positive ambient dimension. |
| C16 | similarity_semantics | §5 change of basis; actual compact-image, radius and product-boundedness invariance. |
| C17 | compound_dimensions | §5 full exterior degrees; basis cardinality and positivity, including k=0. |
| C18 | compound_coordinate_semantics | §5 exterior definition; exact Mathlib algebraic-map/standard-exterior-basis identification. |
| C19 | compound_algebra | §5 chronological exterior words; multiplicativity, identity and empty exterior degree. |
| C20 | compound_norm_bound | Equation(5) lines184–193; fixed dimension-only factor disappears under word-length roots. |
| C21 | compound_local_lipschitz | Equation(10) lines243–253; symbolic minor/telescoping bound on the full closed norm ball. |
| C22 | tensor_algebra | Lemmas3–5 paired tensor products; exact paired word multiplication. |
| C23 | tensor_norm_comparison | Lemmas3–5 norm comparisons; conservative finite constants replace exact Hilbert tensor multiplicativity without changing radii or decay. |
| C24 | allocation_dimensions | §5 lines195–203; actual fiber sizes, degrees<=d and positive allocation-space dimensions. |
| C25 | allocation_algebra | §5 lines195–207; actual diagonal-block word algebra under explicit triangularity. |
| C26 | allocation_product_bounded | §5 lines195–207; every literal allocation family bounded by its actual diagonal families. |
| C27 | compound_allocation_radius | Equation(7) lines205–213; genuine triangular exterior decomposition, all allocations and exact radius maximum. |
| C28 | distinct_allocation_degrees | Equation(8) lines217–222; strict higher/lower degrees of max/min, including ties. |
| C29 | allocation_tensor_norm_bridge | Equations(8)–(9) lines217–235; common-word max/min norm-factor regrouping with a fixed finite constant, including zero factors. |
| C30 | critical_allocation_nonresonance | Equations(8)–(9) lines217–235; strict higher-degree decay implies every actual paired allocation gap. |
| C31 | compound_nonresonance_product_bounded | Lemma5 lines235–239; actual full exterior representation bounded, with its triangularization proved internally. |
| C32 | compound_family_semantics | Equation(5) and §6 lines253–271; actual nonempty compact images, exact radius power upper bound and degree-one equality. |
| C33 | critical_compound_product_bounded | Entire Lemma5 lines184–239; arbitrary normalized reference, no product-boundedness or irreducibility assumption. |
| C34 | compound_hausdorff_bound | §6 lines243–259; both directions of the literal image-Hausdorff formula. |
| C35 | positive_hausdorff_scaling | §6 lines273–278; actual scalar-image Hausdorff equality for every c>0. |
| C36 | root_lower_bound | §6 lines267–271; avoid fractional-power computation while retaining the exact lower estimate. |
| C37 | normalized_pointwise_lower_lipschitz | §6 lines243–271; full normalized reference, arbitrary nearby families. |
| C38 | canonical_pointwise_lower_lipschitz | Canonical unchanged target, solution Theorem(1), §1 and §6; all d>=1, fixed M before constants before N, including rho(M)=0. |

## Numerical minimization and unresolved prerequisites

`NUMERICAL_TARGETS.md` was written and hash-recorded before either new Lean
source. No computation of dimensions, words, permutations, eigenvalues, search
grids or transcendental interval enclosures is planned. The only existing
numerical certificate reused is the exact half-radius inequality. Symbolic
cone bounds, finite geometric sums, determinant telescoping, dimension-only
tensor constants and an elementary root-free transfer suffice. The allocation
norm bridge only regroups factors, so no singular-value computation is needed.

The most substantial **unproved** foundations remain C08/C10 (stable kernel,
quotient and robust cone trajectories), C12/C13 (complete block/nonresonance
theory), C14/C15 (irreducible boundedness and invariant flags), and C27/C31/C33
(the full critical exterior representation). The pinned Mathlib audit found
no ready joint-spectral-radius/Barabanov theorem. Their proofs cannot be skipped
or replaced by assumptions. In particular, completing C10 alone will not count
as MF-06. The draft makes no implementation-effort or completion guarantee.

Two independent nonauthor reviews must check these exact statements and their
definitions. The coordinator alone may run the bounded local statement
typecheck and then freeze the approved corrected boundary. This author-side
correspondence and structural checks are not one of those approvals. Final
proof review and an actual non-root Linux Comparator run remain future gates.

Credit George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; retain Epperlein–Wirth, Barabanov/Wirth,
Chitour–Mason–Sigalotti, Morris and the unchanged MF05/MF07 source attribution.
No email is included.
