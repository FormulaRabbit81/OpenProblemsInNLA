# MI-04 independent review of repair 35067372404

Reviewer: `/root/mi04_independent_referee`; author: `/root`. Independent nonimplementing source review, 16 September 2026.

**Approve this exact source candidate for the next remote build.** No mathematical or statement-preservation correction was found. The remaining timeout has not been shown to disappear. This report does not assert successful compilation, measured performance improvement, Comparator acceptance or complete MI-04 verification.

The approved complete source closure is `4a5983d43ed526ed011499db8246a4332303744d4dda449d359cd81853d08181`. Author MANIFEST: `453f67e52d5cc0134097f720e86fe38572ef61fb58a5ef9ae9c69286960bd4f0`. The predecessor is the previously reviewed closure `6a1ed24745455b6d6b6fa3cc2af95fae85ac853e9003fc35900619dec9dc3a6f`. The independent static audit rehashed the full author inventory, the preceding full-source-review addendum, and the actual runtime audit. External evidence is bound through `EXTERNAL-SEALS.json`, avoiding another copy of the runtime archive.

I read the full current JointBasis file and exact diff. I rechecked the relevant pinned Mathlib declarations for eigenspace membership, actual eigenvalues and their finiteness, orthogonality and completeness of joint eigenspaces, and the subordinate orthonormal-basis APIs. Four primary files were matched by content and Git blob to Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The preceding subordinate-basis proof, definitions, original canonical target and all other 20 source files remain covered by my previous full mathematical review and repair chain.

All 21 before sources match actual Git commit `19e558a9087fc5d9359b28662f8b8b7a9592211c`, run 35067372404's source-bound receipt, and the preceding approved source map. All 21 after sources match the new closure and current author files. Only JointBasis changes. All 165 existing declaration headers remain exact; one private definition and two private proved lemmas bring the total to 168. All ten frozen inputs and all 21 public contracts remain unchanged, as do imports, surrounding section scopes, dependency pins, options and trust assertions. The main declaration still has its scoped 800000-heartbeat allowance; the new helpers have the default bounded allowance.

## Actual failure

The previous run is an authenticated development **failure**, as sealed at `development-runs/35067372404/mi04-independent`. That audit's MANIFEST is `f80267c4a28fc5b43478cbc53505f4acaf21fc0b36b6f70c9a65853ea8523a1e`; the exact receipt is `47136fcd018302191c02a0c4c17dbad242c1a53c3f4dbc1aea0069041ac610e7`. I previously read the entire 511-line MI-04 log and authenticated its source and raw-job provenance. Normality succeeds there. The sole remaining MI-04 diagnostic is JointBasis line 37, declaration-level `whnf` exhaustion at 800000 heartbeats. The subsequent no-axioms print is not accepted evidence. The preceding private subordinate-basis declaration has no reported error, but the JointBasis module as a whole failed.

I executed the batched runtime auditor in that earlier audit. Root reports a subsequent independent rerun producing the same `ROOT-AUDIT.json` hash `7779ed119ea6ae719e0ca26437b573748b73c0c1b76128a90a16e03e08154561`; root's later rerun is not misattributed as another execution by this reviewer. No new Lean execution is performed for this addendum.

## New definition and proof boundaries

`jointEigenSpace A B j` names exactly the previous local family: `eigenspace A j.2.val ⊓ eigenspace B j.1.val`, with `j` ranging over actual eigenvalues of B and A in that order. It introduces no approximation, altered index set or nonzero-subspace restriction.

`jointEigenSpace_orthogonal` proves the same orthogonality assertion formerly held locally. The map from the product of eigenvalue subtypes to the scalar pair is injective: equality of each value yields subtype equality, and the product equality follows. Restricting the pinned orthogonal family of joint eigenspaces along this injective map proves the stated family orthogonal. The helper requires symmetry of A and B, exactly as before; it does not assume the desired eigenbasis or a simple spectrum.

`jointEigenSpace_iSup` proves the exact full-span assertion. Pinned Mathlib's commuting-symmetric-operator theorem says that the supremum over all scalar pairs is the whole space. For each pair, either both scalars are actual eigenvalues and the corresponding joint subspace is included in the restricted supremum, or one eigenspace is proved zero using `hasEigenvalue_iff` and contributes bottom. This removes only zero eigenspaces, retaining every dimension of every repeated eigenspace. Commutation remains an explicit premise of this completeness helper.

The main lemma invokes these proved assertions and the unchanged generic subordinate-basis lemma, then defines the two eigenvalue lists from the returned index map. The new explicit `change` exposes the named joint-space membership as membership in the literal intersection; its two components give the unchanged eigenvector equations via `mem_eigenspace_iff`. Finite-index instances come from the unchanged Minpoly import and product instances; classical decidability is available in the main proof. No new public premise or global instance is introduced.

The construction remains valid in every finite dimension, including the zero-dimensional helper case. For that case the produced basis and index-map domain are empty. The original positive-dimension public problem is unchanged. Singular and zero matrices, repeated eigenvalues and zero intersections remain included. The full canonical conclusion is still the affine-Hermitian representation following from the universal positive-block operator-norm property; neither this helper refactor nor the added private definition weakens that target.

Separating the local orthogonality and spanning proofs into proved lemma boundaries is a reasonable attempt to reduce repeated dependent elaboration. This source analysis does not establish that the new proof fits its finite resource limits. No interval mesh, numerical enumeration, extra computation certificate or kernel exception was added.

## Preparation-history check and scope

The archived author script `repair_mi04_35067372404-before-hash-transcription-fix.py` differs from the corrected script only by one missing `6` in the expected predecessor-closure hash. I checked that the corresponding assertion precedes all source/packet writes and that the corrected script matches the sealed author copy. The author reports the initial attempt stopped there. I did not rerun either author script, and no failed compile was hidden by this correction. Exact historical and corrected hashes are retained in `AUTHOR-TRANSCRIPTION-HISTORY.json`.

The relevant referee requirements remain statement fidelity, explicit assumption/scope checks, edge cases, genuine proved dependencies, and truthful execution provenance. This is independent agent source review, not external human or Tau Ceti certification. Existing Colbrook mathematical credit, George Stepaniants / Caltech Department of Computing and Mathematical Sciences formalization credit, and license notices are unchanged.

No source, development tree, Git reference, PR, publication, count or goal status was changed. No Lean/Lake/cache/Comparator process ran locally. Exact-source compilation and canonical kernel/Comparator/negative/isolation controls remain required before verification can be accepted.
