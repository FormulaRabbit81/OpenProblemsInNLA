# PF-02 independent final source referee 1

**Verdict: APPROVE the complete mathematical source and local kernel/axiom checks.**
Authoritative isolated Linux verification, default-kernel replay and the real
Comparator run remain separate pending gates. This report does not promote the
canonical status or assert that those operational checks have run.

- **Phase:** final source review, 15 September 2026.
- **Reviewer:** OpenAI GPT-6 Codex agent `/root/reference_api_review`, an
  independent AI agent. I implemented none of the candidate proofs. My new Lean
  declarations are audit wrappers outside the proof project, not contributions
  to its proof.
- **Candidate:** `61561dd99c57c7334b3304fa0ad88a51eeac84f2` on `codex/lean-pf02`.
- **Protocol:** the repository's [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md),
  covering correctness, scope, proof quality, reuse, generality, API design,
  naming, placement, documentation and attribution. No official Tau Ceti review
  or external human review is asserted.

## Exact inputs and scope

I read the complete canonical PF-02 page, the preserved manuscript (including
Theorem 1 and its proof), the numerical dossier, all nine Challenge signatures,
all nine `NLA/PF02` source modules, `Solution.lean`, package configuration,
Comparator configuration, README and metadata. The candidate has no substantive
unresolved finding from my preceding exact-boundary review.

The [input record](final-referee-1-evidence/snapshot-inputs.json) lists the exact
SHA256 of every one of the 20 final candidate inputs, all ten frozen pre-proof
inputs and the three original-source context files. I independently compared
these hashes with the current worktree, a fresh source snapshot and the actual
candidate Git objects. Every comparison passed. In particular:

| Input | SHA256 |
| --- | --- |
| Frozen definitions | `2036d380c1881af050bb8fe75328615c405b3745bbdd9bc3c873e7d2c243a2c9` |
| Frozen Challenge | `3b5cc523ed8c883541d57863eaacb9d0e98115186e11ade3f032ec81fc21dd73` |
| Frozen numerical dossier | `09431a3f80e272ab8aa0ec616d2d9223eb771bda14512b0926beac7d13ec1695` |
| Public proof exports | `9c6c37fb4ca5ca4e9c24e711d68fbdef2f73aed34829866985e5bc596a97720e` |
| Solution | `e5549d4bd527ab94821c7b0eba0036788951aac14dd932b697dce5e73920414d` |
| Canonical original page | `4ef3bba41aca6e2a2c66a8a39e5974b54095b85fba0557c6353c253202aa26c7` |
| Complete original manuscript | `7e41f64f8495231b9cadd5296daa8fe44790039d3f6e25260cd04be258f3bf65` |

The historical reviewed-body hash printed inside the manuscript is not the hash
of that complete current file. The record above uses the complete file bytes.
The source, canonical ID/path and full original target remain unchanged. The
canonical status is still **Solved** at this review.

## Complete-target correspondence

`IsFactorization` contains every pair of real PSD row and column families
satisfying every trace equation. It imposes no equality of those two families,
positive-definiteness restriction, normalization, rationality restriction or
orientation condition. `Matrix.PosSemidef` over the reals supplies genuine
symmetry and nonnegative quadratic forms. `IsPSDRank` is an attained `IsLeast`
over every positive integer size and every such tuple. `Matrix.rank` is the
actual ordinary matrix rank.

`Congruent` uses one arbitrary unit of the full real matrix algebra, applying
the prescribed primal and inverse-dual formulas simultaneously to all factors.
`Action.lean` proves these formulas preserve PSD and trace equations for every
dimension and that this relation is precisely equality with one transformed
factorization. `Orbits.lean` proves reflexivity, symmetry and transitivity,
then proves quotient equality iff that single congruence. Thus the use of
`Quot` does not silently enlarge the equivalence classes.

The matrix entries, factor families and their product carry the ordinary finite
product topology of the reals; the factorization subtype has the subspace
topology. The quotient has Mathlib's coinduced quotient topology. The public
quotient-map theorem and the independently checked instances establish the
intended Euclidean subspace/quotient interpretation. There is no substituted
discrete topology on the factorization space.

All nine public statements correspond to the independently frozen boundary:

| Export under `NLA.PF02` | Actual proof and correspondence |
| --- | --- |
| `witness_data` | Literal positive integer 6-by-6 matrix; determinant 8192, actual rank 6, orientations 32 and −32. |
| `witness_factorizations` | Both complete tuples satisfy all trace equations; every displayed factor is genuinely positive definite. |
| `witness_minimal_rank` | A size-three tuple exists; every smaller positive size is excluded, over the full factorization space. |
| `orbit_semantics` | Quotient map and equality iff one actual real invertible congruence, for arbitrary dimensions and matrix. |
| `orientation_nonvanishing` | Nonzero determinant for every factorization of the witness, including singular individual PSD factors. |
| `orientation_preserved` | Sign preserved under every real invertible congruence, including negative determinant changes of basis. |
| `quotient_separation` | Continuous surjection from the entire actual quotient onto the discrete two-point type `Bool`. |
| `witness_disconnected` | Actual failure of connectedness of that quotient, without a path or Hausdorff assumption. |
| `canonical_counterexample` | Negates the complete original universal claim over every k ≥ 3, p,q ≥ 1 and admissible real matrix, by instantiating k=3 and p=q=6. |

The optional manuscript extensions to all factor sizes and strictly positive
rational perturbations are preserved but not claimed as formal results. One
size-three counterexample fully answers the original universally quantified
question; this scope is correctly stated in the dossier and metadata.

## Proof correctness and computation

The witness positivity proof handles every nonzero real vector using its sum of
three squares and exact quadratic inequalities. It checks both signs and all
six factors. The 36 trace equations are exact at both signs. The rank-six proof
uses the determinant 8192 and Mathlib's actual matrix-rank theorem.

For minimality, `trace_factor_rank_le` flattens an arbitrary trace factorization
as a p-by-k² matrix times a k²-by-q matrix. The general bound `rank M ≤ k²`
already excludes k=1 and k=2 when rank M=6. This avoids unnecessary symmetric
dimension machinery while retaining the exact attained-minimum target.

For an arbitrary witness factorization, the actual trace equations yield
`M = U_A G U_Bᵀ`, with trace metric `diag(1,1,1,2,2,2)`. Its nonzero determinant
forces `det U_A ≠ 0` everywhere on the full fiber. The proof uses independent
row and column families, so it does not assume that an arbitrary factorization
is a Gram tuple like the explicit examples.

`congruence_covariance` proves all coordinates of `Sᵀ X S` for an arbitrary
real symmetric X and arbitrary real S. The subsequent determinant theorem
proves `det C(S) = (det S)^4` for all nine independent real entries, including
singular S. Unit invertibility is used only afterwards to make the fourth power
strictly positive. There is no restriction to diagonal matrices, sampled
matrices, orthogonal transformations or the positive-determinant subgroup.

The determinant sign is locally constant on the whole fiber because zero never
occurs. Congruence invariance gives a genuine `Quot.lift`; the standard
continuous-quotient-lift theorem proves its continuity. The two explicit tuples
give both Boolean values. A connected image in the discrete two-point space
would be a singleton, contradicting surjectivity. This is sufficient to prove
actual disconnectedness.

LeanCert's `interval_decide (trust := kernel)` proves `0 < (32 : ℝ)`.
`orbitSign_surjective` actually consumes this theorem in both sign branches;
it therefore lies in the final counterexample's proof dependency chain.
The imported LeanCert trust checker uses transitive `collectAxioms` and rejects
native-compiler, sorry and custom axioms in kernel mode.

I inspected the pinned `norm_det`/`eval_det` implementation: it constructs
kernel-checkable equality certificates using the proved
`BirdDet.det_eq_birdDet`, then proof-producing ring normalization. The local
symbolic determinant computation took 7.1 seconds in the fresh module build.
No floating-point tolerance, sampled interval, external algebra output, custom
axiom or native compiler oracle replaces any target proof.

My separate exact arithmetic program, first written before reading the author's
checker, was rerun independently. Its **48 checks passed**. These include both
complete trace factorizations, exact ranks/determinants, all 12 real quadratic
form identities and a separately derived nine-variable congruence polynomial
with all **120 degree-12 terms** matching `(det S)^4`. This diagnostic supports
the review; Lean proofs establish the mathematics.

## Independent local execution

I built a fresh source snapshot without copying any project `.lake/build`
artifacts. Its dependencies reused the existing package cache; all ten Git
revisions matched the manifest and had no tracked changes. This is a fresh
project build, not a claim of a cache-free dependency build or isolated Linux
execution.

- Lean **4.33.1**, compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Darwin arm64.
- `lake build Challenge`: exit 0, 2062 jobs, exactly nine intended
  specification-placeholder warnings. These establish no proofs.
- `lake build Solution`: exit 0, 3649 jobs, no warnings. All project proof
  modules were newly built.
- `lake env lean AuditFull.lean`: exit 0. I copied all nine exact frozen
  Challenge types under distinct audit names and assigned the actual exports.
  Those nine wrappers and 23 substantive auxiliary declarations passed **32**
  `#assert_trust kernel` checks and **32** printed transitive axiom checks.
  Every printed closure contained only `propext`, `Classical.choice` and
  `Quot.sound`.
- The audit also synthesized the actual discrete Bool, factorization-subtype
  and quotient topologies. No proof source imports Challenge; the proof source
  scan found no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by` or
  new axiom declaration.
- Metadata schema and exact Comparator coverage passed for all nine exports.

The [execution record](final-referee-1-evidence/execution-record.json),
[audit harness](final-referee-1-evidence/AuditFull.lean), fresh logs, independent
arithmetic script/output and source-hash validation script are retained in
[the evidence directory](final-referee-1-evidence/README.md), sealed by
[SHA256SUMS](final-referee-1-evidence/SHA256SUMS).
The execution-record SHA256 is
`5407cac2478c161abed53fc21504a0aa7c00323d860e6fa4b060e0e93536cbaf`.

These exact-type assignments are additional local evidence. They do not replace
the scheduled Comparator comparison of independently exported environments or
its default-kernel replay and negative controls.

## Reuse, API, documentation and attribution

The implementation reuses Mathlib's PSD congruence facts, trace cyclicity,
ordinary rank bounds, determinant correctness, quotient topology, continuous
lifting and connected-image facts. I checked the relevant pinned APIs and
searched for an existing congruence-determinant implementation; no directly
applicable existing formula was found in that search. The specialized
three-dimensional coordinate identity is proportionate to this counterexample;
the generic change-of-basis, orbit and trace-rank facts retain their natural
dimension generality. Definitions contain mathematical predicates, not hidden
conclusions or certifier shortcuts.

Module names and lemma names expose their role. The split between data,
coordinates, symbolic determinant, generic action/rank/orbits, topology and
public exports is coherent. `Action.lean` includes explicit semantics beyond
the bare public counterexample and was separately kernel-audited. The local
heartbeat increase is confined to the symbolic determinant theorem.

The README accurately distinguishes candidate/source checks from authoritative
Linux verification, explains the exact computation reductions, documents the
explicit Solution build and warns that the default Challenge build alone proves
nothing. Comparator has nine theorem names and no replaceable definition holes.
Metadata truthfully records zero proof sorries, all permitted axioms, substantial
AI assistance, independent AI reviewers and unclaimed optional extensions.

George Stepaniants and the complete Department of Computing and Mathematical
Sciences, California Institute of Technology affiliation appear in the new
formalization attribution. No contact email was added there. Matthew J.
Colbrook's original mathematical authorship and the complete original source
are preserved. The historical manuscript's own authorship details remain intact.
Reference-project usage is correctly described as structure/API reuse; no
uncredited mathematical implementation copying was found.

## Remaining gate

**No blocking source finding.** This approval is specific to the recorded
candidate bytes. The other independent source approval and actual reproducible
Linux/Comparator/default-kernel/permitted-axiom checks, including the operational
negative controls, must close before promotion to **Lean verified**. Publication
stage wording may then be updated without changing the frozen mathematical
boundary or proof; any such changed documents require their own exact-byte
stage supplement.
