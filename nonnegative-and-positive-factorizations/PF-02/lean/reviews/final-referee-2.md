# PF-02: independent final source referee 2

**Verdict: PASS — complete-target source candidate approved.** No mathematical, correspondence, proof, or attribution changes requested. **This is final source approval only; isolated Linux/Comparator verification and independent operational review remain pending.** It does not by itself promote the canonical status.

Reviewer: **OpenAI Codex AI agent `/root/existing_verification_audit`**, 2026-09-15. I independently approved the pre-proof statements and contributed no proof or definition code. I cover fidelity, correctness, proof quality, numerical correspondence, reuse/API, documentation and attribution under [the repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md). This is AI-agent review, not external human peer review or official Tau Ceti endorsement.

## Candidate and independent evidence

Reviewed commit: **`61561dd99c57c7334b3304fa0ad88a51eeac84f2`**, independently confirmed as the worktree HEAD. The exact [20-input candidate record](final-source-inputs.json) has SHA-256 `d1ba7015635abb5765dc34e5f32cc31f3a4272204f2317bf32d76171cc500dc1`.

My [review evidence](final-referee-2-evidence/review-evidence.json), SHA-256 `9fdf7e22c98c7b57552cab2d41a68eb0a44f6d18e1ae60ae834601ce06badfc2`, records every reviewed input and original-source hash, every independent command and result, the actual axiom closures and every evidence-file hash. All 20 candidate inputs, all ten pre-proof frozen inputs and all three canonical/source/review files were independently rehashed after my checks and remain unchanged.

Key completed proof hashes:

| File under `NLA/PF02/` | SHA-256 |
| --- | --- |
| `Action.lean` | `637b8a03fa25bc87e5ec71ad492ea507cf3fdd96483c117474a83439353149ad` |
| `CongruencePolynomial.lean` | `f786a773415fab784cd11b8b54ecf65076e800aa726266cdb2b15d3b63f5394c` |
| `Coordinates.lean` | `fce4bd15d0321bae1f34488d0d162f2a4d584b4aed796898ef2303e791d6f018` |
| `Data.lean` | `28418a59c8894408a31a74578a2d75eff0005893caecbcf54ff1f01fca3d5880` |
| `Orbits.lean` | `9a5920e32771d07d366d9fe3230c17ed8aa6847f59f9bc7a47bc61e4e4197275` |
| `Proof.lean` | `9c6c37fb4ca5ca4e9c24e711d68fbdef2f73aed34829866985e5bc596a97720e` |
| `Rank.lean` | `b8df248b437538ba056730648d43d3b6395c395735d29a1637c2a559486060a3` |
| `Topology.lean` | `97f1bccb4e3abd2a32217be570115556c12b960e7b6d0b9b4bc18bf3192104a8` |

I read every actual proof module, Definitions, Challenge, Solution, project README and metadata. I compared them with the unchanged complete canonical statement, complete source manuscript previously read, numerical dossier and both pre-proof obligations. No desired conclusion has been inserted into a definition or hypothesis.

My independent mechanical checks were:

- Copy exact sources into a new separate project, with no existing project objects; run pinned Lean **4.33.1** `lake build Solution Challenge`, exit **0**. All project modules freshly compiled. Only the nine intentional Challenge specification holes produce warnings. [Actual build log](final-referee-2-evidence/fresh-build.log).
- Run a separate [FinalAudit.lean](final-referee-2-evidence/FinalAudit.lean), exit **0**: **35** explicit kernel-trust assertions and transitive axiom reports, including all **nine** exports and 26 semantic/certificate lemmas. Every closure contains exactly **`propext`, `Classical.choice`, `Quot.sound`**. [Actual output](final-referee-2-evidence/final-audit.log).
- Recheck the actual topology instances in the completed environment: discrete Bool, inherited factorization subtype and coinduced `Quot` topology. No proof module changes those instances.
- Match all nine final theorem type signatures with Challenge exactly. [Source-signature record](final-referee-2-evidence/signature-check.json). This is a supplementary source comparison, **not Lean4 Comparator**.
- Rerun my own independent arithmetic and full nine-variable symbolic reconstruction, exit **0**, reproducing my pre-proof result byte-for-byte. [Checker](final-referee-2-evidence/independent-check.py), [result](final-referee-2-evidence/independent-check.json). This supports numerical review; the actual Lean proofs establish the quantified results.
- Run the metadata/schema and Comparator-coverage validator myself, exit **0**, nine declarations covered. [Log](final-referee-2-evidence/metadata-validation.log).
- Inspect the proof imports and search for holes, additional axioms and unsafe/native proof shortcuts. None occur in project proof development; Solution never imports Challenge.

These are fresh **local project-source** builds using existing pinned dependency objects. They are not independent dependency rebuilds or Linux sandbox/Comparator runs.

## Exact scope and full factorization space

The universal proposition retains every k≥3, p,q≥1, entrywise nonnegative real matrix M, ordinary rank k(k+1)/2 and actual minimum PSD factor size k. It asks connectedness of the entire real congruence quotient. `canonical_counterexample` supplies the actual positive 6×6 witness, rank-six theorem, attained PSD rank three and proved quotient disconnectedness to contradict that unchanged proposition.

One k=3 counterexample is sufficient to negate this universal question. The source's optional constructions for all factor sizes and positive rational perturbations are not claimed; metadata explicitly distinguishes this scope while preserving the complete original manuscript. The ordinary-rank condition is retained rather than bypassed with a disconnected nonnegative-factorization example at a different rank.

`IsFactorization` still includes all independent row and column families of real symmetric PSD matrices satisfying every trace equation. It imposes no individual nonsingularity, positive definiteness, equality between the families, normalization or entrywise factor nonnegativity. The two displayed PD tuples are witnesses inside that full space, not its definition. In particular, the negative off-diagonal entries of the reflected tuple are allowed.

## Exact witnesses, trace pairing and genuine minimum size

`witnessFactors_posDef` first proves real symmetry and then positivity of the actual quadratic form for every nonzero real vector. The sum of the three squared coordinates is strictly positive because a nonzero vector has a nonzero coordinate. The remaining finite quadratic inequalities prove every factor for both signs. It does not infer positive definiteness merely from positive entries or sampled test vectors.

`witness_trace` checks all 36 trace constraints at each sign, and `explicit_factorizations` supplies both complete row/column tuples. The actual matrix is entrywise strictly positive. Exact determinant calculations give coordinate determinant `32*s` for every real sign parameter s, det M=8192, and actual ordinary rank six via Mathlib's nonzero-determinant theorem.

`trace_factor_rank_le` flattens **arbitrary real** k×k row and column factors into rectangular U,V with inner index `(Fin k × Fin k)`. The column entries reverse the two indices, precisely matching `trace(A_i B_j)`. It proves M=UV and hence rank M≤k² using actual rank-product/cardinality bounds.

`minimal_three_of_rank_six` applies this universal bound to every feasible positive size below three, ruling out both one and two. The supplied size-three PSD tuple establishes membership in the feasible-size set. Thus the exported `IsPSDRank witnessM 3` is the actual **IsLeast**, including attainment and the bound against all feasible sizes. This simpler sufficient bound does not weaken the PSD-rank conclusion.

`trace_coordinate_identity` has both symmetry hypotheses and correctly doubles off-diagonal terms through `diag(1,1,1,2,2,2)`. Applying it to arbitrary PSD row and column families proves M=U_A G U_Bᵀ on the entire factorization space. Taking determinants and using det M=8192 proves the orientation determinant is never zero for **any** factorization, including ones with singular individual factors or unrelated primal/dual families.

## Every real congruence and the exact orbit relation

`changeBasis_preserves_factorization` proves preservation for arbitrary p,q,k and every real invertible matrix unit S. It reuses genuine PSD congruence theorems for both primal and dual families. The trace calculation uses the actual inverse, matrix associativity, cyclic trace and inverse-transpose cancellation; its order is Sᵀ A S and S⁻¹ B S⁻ᵀ, exactly as in the canonical problem.

The subtype transformation is constructed from that proved preservation. `congruent_iff_changeBasis` then identifies the frozen relation with equality to one actual transformed factorization. Separately, Orbits proves reflexivity, symmetry via S⁻¹ and transitivity via **S*T** for applying S and then T. `actual_orbit_eq_iff` reduces the generated equivalence relation of Lean's `Quot` by these proved properties. Consequently quotient equality is equivalent to a single genuine full-GL congruence; no enlarged equivalence, normalized orbit, or smaller group is substituted.

The topology is Mathlib's actual coinduced quotient topology of the Euclidean factorization subtype. `actual_orbit_semantics` proves the projection is a quotient map and exports the exact equality bridge for every dimension and M. No Hausdorff assumption is made.

## Fully symbolic sign preservation and genuine disconnectedness

`congruence_covariance` verifies every coordinate of Sᵀ X S for every real S and symmetric X. `rowCoordinates_congruence` applies this same coordinate transformation to every factor in an arbitrary real family. The generic `congruenceCoordinates_det` then proves

`det (congruenceCoordinates S) = (det S)^4`

for **all real 3×3 S**, including singular ones. The nine entries remain arbitrary variables throughout; this is not a table of sampled congruences. My independent symbolic reconstruction agrees with the entire polynomial identity.

For an actual unit S, its determinant is proved nonzero, so the fourth power is positive without requiring det S>0. `orientation_congruent` therefore preserves the orientation sign even under orientation-reversing changes of basis. It uses the actual coordinate determinant of the full row tuple.

`continuous_orientationDet` is continuity of the actual coordinate determinant on the subtype. `continuous_fiberSign` uses open positive and negative determinant neighborhoods, with all-factorization nonvanishing justifying the negative case. It proves a locally constant Boolean sign on the whole fiber. `fiberSign_congruent` proves it constant on every actual orbit, so `Quot.lift` and `continuous_quot_lift` give an actual continuous function on the quotient.

Surjectivity is proved with the two genuine factorization subtypes and their exact determinants ±32. The positive constant is supplied by the explicitly kernel-mode LeanCert theorem `thirty_two_pos`; that theorem is actually consumed in both sign witnesses. This closes the pre-proof requirement that LeanCert be connected to the target.

Finally, a connected quotient would have connected/preconnected image in discrete Bool, hence a subsingleton image. Surjectivity puts both false and true in it, giving a contradiction. This proves **actual disconnectedness**, with explicit nonempty separated values; it is not merely a failure of path connectivity or a claim that the two tuples are inequivalent. The final universal negation supplies all original hypotheses.

## Reuse, trust, documentation and attribution

I inspected the pinned `Mathlib.Tactic.NormDet` implementation. `eval_det` uses the proved Bird determinant identity, certificate-chain evaluator and ring normalization to construct proof terms. It is not a native-evaluation oracle. The completed generic determinant theorem and every public result pass my own transitive kernel/axiom audit.

The implementation reuses Mathlib PSD congruence, rank, determinant, quotient and connected-image APIs. The module split separates data, generic coordinates, the determinant polynomial, full congruence action, rank, orbit semantics, topology and final exports. The k² rank bound, sparse quadratic reasoning and specialized symbolic determinant avoid unnecessary general representation or perturbation theory without reducing the canonical target. The Forsythe/Schiffer structure/API references and actual checker reuse are documented without claiming copied mathematical implementation.

The canonical README, complete original manuscript and permanent ID registry are unchanged from the published base. ID **PF-02** and its canonical path remain intact. New headers and metadata credit **George Stepaniants**, **Department of Computing and Mathematical Sciences, California Institute of Technology**, disclose substantial AI assistance, and preserve **Matthew J. Colbrook** as the original counterexample author. No new contact email is supplied. Historical source attribution is preserved.

README and metadata truthfully describe a complete local candidate with pending independent final/operational gates. All nine main results are listed with the observed standard axioms. The zero proof-development sorry count explicitly excludes the nine specification placeholders. The unchanged default Lake target remains Challenge, and reproduction instructions explicitly build Solution and explain why Challenge alone is insufficient. No human review, author endorsement, novelty, unmeasured cost or official Tau Ceti endorsement is asserted.

The earlier dossier export-name mismatch was resolved before the frozen boundary, and remains resolved. Every substantive pre-proof obligation now has an actual implementation and independent local verification. No source finding remains open.

## Remaining operational gate

**Full-source PASS for the exact candidate above.** Preserve this mathematical boundary for the fresh committed-input Linux run. Actual Lean4 Comparator against the frozen Challenge, default-kernel replay, permitted-axiom/rejection controls, artifact/source provenance and both independent operational reviews are still required. I claim none of those future runs. Canonical status remains **Solved** until those separate checks succeed and publication metadata is updated truthfully.
