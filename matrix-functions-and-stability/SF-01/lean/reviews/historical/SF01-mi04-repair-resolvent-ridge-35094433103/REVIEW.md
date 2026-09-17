# Independent SF-01 repair and symbolic-prefix review

Reviewer: `/root/mi04_independent_referee`, a nonauthor of these SF-01 sources.
Verdict: **approve these exact sources for the next controlled development
build**. No mathematical correction was found. This is source review, not a
claim that the repaired or new proofs have compiled. SF-01 remains incomplete.

The effective candidate is the 25-file graph selected by
`next-proofs/SF-01/proof-handoffs/ridge-05/SOURCE-PATHS.json`, with closure
`acfcae3890e71d48bd2be339faaa3a55fd2411a41ec4c759efc73a30fa0a2290`.
It includes the observed two-body repair, all four resolvent modules and all
four ridge modules. I read both changed files and all eight new modules in
full, the frozen definitions, all 24 Challenge contracts and numerical
obligations, and the relevant previously reviewed weight/spectrum dependencies.
This continues my original full-target, foundation, converse and foundation-
repair reviews; it does not replace those reviews with the author's summary.

## Exact boundaries and evidence

The independently executed static audit passes 877 checks. It authenticates
all three packet inventories and their retained external bindings, all 25
selected source hashes, the exact import closure from `RidgeChecks`, all nine
frozen inputs and all 24 contracts. The observed repair preserves all 109
existing declaration headers. The final prefix has 126 declaration headers;
14 public implementations have exact frozen signatures and ten remain absent.
No section assumption, modified comparison predicate, reduced export list,
admission, new axiom, native trust mode or resource-limit change is introduced.
These are static checks; actual kernel/Comparator acceptance remains required.

Each four-module addition matches its recorded seventeen-signature plan.
The ridge plan preceded the actual repair; its separate append-only
`BASE-REFRESH-BEFORE-CODE.json` explicitly selects the repaired 21-file base
before ridge implementation. The new eight modules total 568 lines. Earlier
Numerical/Complexification repair snapshots and the two new repair snapshots
are selected explicitly, rather than the intentionally stale original author
files. All 21 original workspace files remain unchanged. Sealed packets remain
immutable.

Seventeen distinct primary Mathlib files are checked against literal commit
`0df444a360eaa60ab8c11dca51a86af692955474`; the precise relevant API ranges were
read, and full-file hashes are bound. Original canonical SF-01 README and
manuscript bytes are checked against their recorded Git commit. The original
problem is still the uniform preservation claim for the actual Newton
iteration on real H-matrices with positive diagonal. This prefix neither
redefines the spectral H-matrix predicate nor pretends its final Newton claim
has been proved.

## Observed repair

The actual failed run is
[`35094433103`](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35094433103)
at literal `a6ff104e8a050cf5d22d08e55e1818e0228906ad`, job `104788187776`,
artifact `10446150263`. I read the complete 58-line SF module log and 24-line
Challenge log, reconciled the actual raw-job diagnostic markers, ZIP contents,
API identities, all eleven command postmaps and all 17 executed SF source
blobs with Git and the receipt. Root's separate all-1,957-input Git audit is
retained with its true `/root` executor label; I do not claim to have rerun that
larger audit.

`WeightedSpectrum` had applied `.mp` to the function `mul_le_mul_right`. The
replacement uses the pinned `mul_le_mul_iff_left₀` equivalence to cancel the
strictly positive right factor `‖z i‖`. Nonzero `z i` is actually proved by the
maximum weighted eigenvector construction; no new positivity assumption is
added. `UnitWeightContinuity` now states the definitionally equal finite row
sum before applying `Finset.sum_nonneg`, resolving the observed ambiguous
finite-set/type goal. The two edits preserve their entire headers and proofs
outside those expressions.

The historical SF module command failed. Its foundation and Numerical modules
did build, including the actual half-certificate/initial-data axiom output with
only `propext`, `Classical.choice`, and `Quot.sound`. The 24 Challenge warnings
are intentional statement holes and are not completed proofs. None of the
eight new resolvent/ridge modules was in this execution; Comparator was not
run. The first local audit attempt used straight quotes when matching Lean's
backtick-delimited warning text; that audit-only matcher was corrected before
the successful audit and seal. No proof or historical log changed.

## Mathematical continuation

For the resolvent prefix, adding a nonnegative shift preserves the comparison
matrix identity and the positive weighted row image. The existing proved
weighted-Z converse constructs the original spectral M-matrix property, and
the comparison-weight theorem proves actual unitness. The absolute row
comparison separates the diagonal term from the erased finite sum and applies
ordinary triangle inequalities; its general helper needs no diagonal-sign
assumption. The frozen shifted theorem retains its original hypotheses.

The inverse comparison is proved using genuine inverse-column equations only
after both shifted matrices are shown to be units. Writing `S*x=e_j` and
`C*z=e_j`, absolute comparison gives `C*|x|≤e_j`; thus `C*(z-|x|)≥0`. The
previously proved weighted-Z maximum principle yields `z≥|x|`, exactly the
entrywise resolvent conclusion. No monotonicity of a totalized inverse, extra
interval regularity, approximate inverse or sampled spectral property is
assumed.

For the ridge prefix, both left and right actual inverse equations give
`A*(A+tI)⁻¹=(A+tI)⁻¹*A=I-t*(A+tI)⁻¹`. This establishes commutation for each
rational term and its finite weighted sum. For a weighted Z-matrix, the shifted
inverse is nonnegative; the rational factor is Z, and its action on the
positive weight equals the shifted inverse applied to the original positive
row image. The strictly positive `a*v` term then gives a strictly positive
ridge row image. Positive diagonal is derived from that row image and the
nonpositive off-diagonal sum, rather than assumed.

The diagonal comparison correctly reverses the inverse bound through
subtraction from the identity. The off-diagonal comparison bounds absolute
values by the negative comparison-factor entries. Nonnegative weights preserve
both bounds under finite summation. Positive diagonal on the comparison side
forces positive diagonal for the actual ridge matrix; entrywise comparison
transfers the positive weight. The existing spectral converse and actual unit
theorem then supply all seven conjuncts of `ridge_comparison_preserver`.

The reasoning includes all dimensions in the frozen statements, `t=0` in
nonnegative-shift helpers, empty pole families, zero coefficients and repeated
poles. There is no division by a coefficient or shift and no unjustified
ordering/distinctness assumption. All spectral quantities remain the actual
complex spectrum. The route is symbolic and adds no interval subdivisions or
numerical computation. The existing LeanCert half certificate and its consumer
are unchanged.

## Attribution, remaining work and operational scope

Matthew J. Colbrook retains the original mathematical attribution. George
Stepaniants retains SF-01 formalization credit at the Department of Computing
and Mathematical Sciences, California Institute of Technology, with AI
assistance disclosed. Sidney Holden's two reused IV-03 files and Apache-2.0
license remain byte-identical and attributed. No contact information is added
to new proof sources. Original source material is bound privately, not
republished by this review.

The ten remaining contracts are `pole_positive_definite`,
`pole_diagonalization_exists`, `pole_residue_normalization`,
`reciprocal_weights_nonnegative`, `reciprocal_blocks_isUnit`,
`matrix_reciprocal_identity`, `newton_data_step`, `newton_first`,
`iterate_ridge_representation`, and `canonical_newton_preservation`. No complete
Solution is advertised. The scope-relevant Tau Ceti checks—semantic fidelity,
noncircular definitions, explicit hypotheses and edge cases, trustworthy proof
boundary, provenance and independent review—find no source-level blocker.

I executed no Lean, Lake, cache operation or Comparator; changed no author
source, shared worktree, Git state, CI, PR, problem status or count. Root owns
the sole serial local build and the later exact-publication verification gate.
The relative-path inventory in `MANIFEST.json` binds this report, its audit
script, checks and all retained source/evidence dependencies.
