# MF-22 independent complete-source and publication review

Reviewer: OpenAI Codex agent `/root/mf22_publication_referee`, acting as an
independent nonimplementing referee. I did not write or repair any MF-22
mathematical source. This is automated-agent review, not human peer review or
an official Tau Ceti review-service result.

Reviewed candidate: `c701bfeea660473fc31ad9d0c74b76309be3b49f`,
`matrix-functions-and-stability/MF-22/lean`. The exact 29 implementation-file
hashes, frozen boundary checks, metadata hash and measured development evidence
are in `CHECKS.json`; `check_sources.py` records the checks actually executed.

**Verdict: approve the complete mathematical source. Standalone canonical
runtime acceptance and final publication reconciliation remain pending.**
There is no unresolved mathematical finding on these bytes. This source
approval alone authorizes neither a verified-count increment nor a claim that
Comparator or default-kernel replay has passed.

## Reading and scope

I read all 29 active implementation files in full, the entire separate
22-contract Challenge, all definitions, the original canonical problem and
complete retained manuscript, numerical targets, source correspondence,
proof architecture, metadata, project instructions and review protocol.
The immutable upstream source is bound by `SOURCE-PROVENANCE.json` at
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. I checked these sources against
Git and against the unchanged canonical statement/manuscript in the candidate.

The target is every fixed positive real parameter, all sufficiently large
matrix sizes, eventual nonsingularity and an existential nonnegative
polynomial exponent for the genuine complex Euclidean condition number.
The formal proof chooses exponent **2**. This proves the entire original
question; it does not certify the stronger exponent **1** in the manuscript.
The candidate README and metadata make that distinction explicitly. No
parameter interval, exceptional-parameter deletion or sampled-size result
replaces the original quantifiers.

## Mathematical checks

* The eight literal coefficient blocks, integer offset `j-k`, factor 80,
  complex field and `Fin n × Fin 2` indices match the original family.
  `spectralNorm` uses the actual induced Euclidean continuous linear map.
  `conditionNumber` is infinite at determinant zero. The final theorem also
  proves nonzero determinant; totalized matrix inversion cannot mask a
  singular case. Constants precede the universal running size and cannot
  depend on it. The eventual threshold is at least one.
* `SourceRows`, `Coordinates` and `SourceRecurrence` establish equivalence
  with the literal finite matrix equation for arbitrary right-hand sides.
  Zero extension gives exactly the required three left values and `u_n=0`.
  No artificial condition on `v_n` is introduced. The final `v` coordinate
  is recovered using state `j+1`, including state `n`.
* The fixed two-dimensional inverse is justified by its nonzero determinant.
  Exact four-dimensional determinant, cofactor and characteristic-polynomial
  calculations relate the actual transfer matrix to the explicit source
  polynomials. `Coprime` discharges both elimination branches, with nonzero
  denominators proved before cancellation. No external root theorem from
  the informal manuscript is assumed.
* The real-cubic argument proves existence of a real root and a nonreal
  conjugate pair. Exact Cayley norm identities give the interior, unit and
  exterior roots. The case `rho^2=10` is separately handled by the quadratic
  plus the root `-1`; nonzero leading scalar excludes the Cayley pole.
  Four roots are proved distinct and nonzero. `RootData` is consumed only
  after its unconditional existence theorem is supplied in the final path.
* Projectors are evaluations of actual Lagrange basis polynomials at the
  transfer matrix. Nodal divisibility and Cayley–Hamilton prove the complete
  decomposition, including power zero. Simple-root multiplicity bounds the
  eigenspace dimension and proves the rank-one boundary sandwich. The
  adjugate, left/right eigenmatrix identities and cyclic trace then prove
  the boundary scalar nonzero via the proved coprimality result. The proof
  does not infer this sandwich from idempotence alone.
* The nondominant powers are uniformly bounded. Qualitative geometric growth
  gives a parameter-dependent threshold and controls the actual normalized
  boundary scalar. No numerical search for a threshold or approximate
  eigenvalue is used. Natural-subtraction powers in Green terms are either
  guarded by `ell<j` or used with `ell<n`; the exponent comparisons are
  justified before the ratio bounds are applied.
* The Green formula is proved to reconstruct every source state and to be
  an actual right inverse. Finite square-matrix identities give the other
  inverse assertions. Returning to the original matrix explicitly restores
  the inverse factor 80. The growing projector terms cancel before entry
  estimates. The remaining products have fixed inner dimension four, so
  one constant bounds every Green entry over all growing dimensions.
* The inverse-entry theorem covers both within-block coordinates. Finite
  Cauchy–Schwarz bounds both genuine operator norms by dimension times the
  entry bound. The dimension is exactly `2n`, yielding a positive constant
  multiplying `n^2`. The final real-power conversion supplies exponent 2
  without changing any hypothesis. The final path has no conditional
  spectral datum, unproved bound or theorem hidden in a definition.

## Computation, reuse and scoped Tau Ceti assessment

I read the pinned Tau Ceti correctness, scope, proof-quality, reuse,
generality, API, naming, placement, documentation and attribution rubrics,
applying this repository's documented scope adaptation. NLA's permanent
problem path and one-problem submission govern placement; Tau Ceti roadmap
admission and its own namespace/directory policy do not govern this project.

The implementation reuses Mathlib's Euclidean matrix maps, finite
Cauchy–Schwarz, complex root existence, Lagrange interpolation,
Cayley–Hamilton, root multiplicity, eigenspace dimension and actual inverse
APIs. I searched the pinned local Mathlib for the corresponding norm,
interpolation, polynomial sign and eigenspace APIs. The displayed source
uses those foundations rather than assuming missing mathematical results.
No directly substitutable existing full MF-22 proof was identified by this
bounded API review; it is not a new exhaustive public-fork search.

Helpers are grouped along the actual proof path, with mathematical comments
explaining the fixed-size reductions and boundary handling. The source has
routine linter warnings (unused arguments/simp entries and harmless tactic
sequencing); these do not weaken the frozen statements or bypass kernel
checks. The thin public export conjunctions preserve the required independent
contracts. No speculative API redesign or unneeded change to that boundary
is requested by this review.

The completed-square identity reduces unbounded-parameter positivity to the
single positive integer margin 5280431. LeanCert's kernel certificate for
that margin is consumed by `positive_discriminant_factor` and ultimately
the main result. There is no interval grid, growing determinant computation
or floating-point root search. Every advertised export has an explicit
kernel trust assertion and axiom report in the implementation entry point.

## Executed evidence and publication limits

I inspected the complete MF-22 development compiler log from run
`35052024095`, including the final `NLA.MF22.Complete` success and all 22
permitted-axiom reports, and the separate Challenge log. The combined
workflow failed because other problem components failed; the MF-22 component
completed with exit code zero. The development workflow did **not** run
Comparator. Its green component cannot stand in for the canonical gates.

My executed Python checks independently compare every one of that run's
1118 receipt inputs against the actual development Git commit, all nine
command log hashes and unchanged post-command source manifests, ten
dependency revisions, all 29 current implementation bytes against the
accepted component and candidate Git commit, all 22 exact contract headers,
the ten original frozen snapshots, and all recorded package-file hashes.
The final complete component reports only `propext`, `Classical.choice` and
`Quot.sound` for every export. Current schema-v0.4 metadata validates and
truthfully keeps standalone Comparator/default-kernel/control acceptance
pending. I executed no local Lean, Lake or dependency/cache operation.

The sole amended frozen configuration is the active Lake default from
Challenge to Solution; the original snapshot remains intact and dependency
pins are unchanged. Frozen statement-phase documents deliberately retain
their dated proof-free descriptions. They must be read as historical
boundary records, as the freeze and current README explain.

George Stepaniants is credited with the Department of Computing and
Mathematical Sciences, California Institute of Technology affiliation.
The original family, question and source root-classification authors retain
their credit. AI assistance and automated review are disclosed, and the
candidate commit uses no email. Schiffer, Forsythe and the checking-tool
contributors are acknowledged without claiming imported mathematical proofs.

Before a final publication claim, inspect the actual standalone canonical
run, its exact source-bound receipts, Comparator, default-kernel replay,
permitted-axiom reports and sandbox/rejection controls. Then reconcile the
final documentation and exact published bytes. The active metadata's old
draft-only `verification.publication` sentence should be replaced at that
transition with the actual publication state. This review changes no source,
canonical status, catalog, PR or verified count.
