# PF-02: independent statement referee 2

**Verdict: APPROVE the exact mathematical and numerical boundary for proof implementation.** This approves the statements and proposed certificate identities, not a Lean proof, completed formalization, Comparator result or status promotion.

Reviewer: **OpenAI Codex AI agent `/root/existing_verification_audit`**, 2026-09-15. I am an independent non-implementing referee and wrote no PF-02 proof or definition code. The arithmetic diagnostic below is my own separate review computation. This review follows the repository's Tau Ceti adaptation; it is not external human peer review or official Tau Ceti endorsement.

## Exact bytes and independent checks

The reviewed package is [statement-inputs.json](statement-inputs.json), SHA-256 `dd24b6567e30c3d781a17a5b11574b64ddb007e15b2b5264630630e010386c06`. I independently verified all ten listed input hashes and the three original canonical/source/review hashes. The [review evidence](statement-referee-2-evidence/review-evidence.json), SHA-256 `d62495d54dbb0c0756bf25555a1ad9e137b385f906d749c227d24da35bb3bb34`, records the complete hash lists, dependency pins and checks.

| Exact boundary file | SHA-256 |
| --- | --- |
| `NLA/PF02/Definitions.lean` | `2036d380c1881af050bb8fe75328615c405b3745bbdd9bc3c873e7d2c243a2c9` |
| `Challenge.lean` | `3b5cc523ed8c883541d57863eaacb9d0e98115186e11ade3f032ec81fc21dd73` |
| `NUMERICAL_TARGETS.md` | `09431a3f80e272ab8aa0ec616d2d9223eb771bda14512b0926beac7d13ec1695` |
| `comparator.json` | `4b3b915c2a15d6d0af4d025dcb61196c1ed4a5559fd0d3ca5179314b331775c7` |
| `lakefile.toml` | `711f93e05247cf5e744f1283c1bc6e9929436bb4bf452b3875e381bda31994f9` |
| `lake-manifest.json` | `19b43bd134b48c326c0977c6134db0c9a7da9fc89961d20cd303390ac7154eda` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

I read the complete canonical README, complete Colbrook manuscript including its extensions, prior source review, full dossier, Definitions, all nine Challenge types and Comparator configuration. I also directly checked the original [Fawzi et al. question in §9.2, Problem 9.4 and the congruence action in §7](https://arxiv.org/html/1407.4095#S9.SS2): the maximal ordinary-rank condition and real GL orbit question agree with the retained canonical target.

I copied the exact Lean sources and pins to a fresh separate project and ran pinned Lean **4.33.1** `lake build Challenge`, exit **0**. Definitions and Challenge were freshly compiled; only the **nine intentional specification placeholders** produced warnings. I separately printed the elaborated boundary and synthesized its actual topology instances, exit **0**. The resulting instances are the real discrete Bool topology, the inherited subtype topology and the genuine `Quot` topology. [Build log](statement-referee-2-evidence/statement-build.log), [audit source](statement-referee-2-evidence/StatementAudit.lean), [elaborated output](statement-referee-2-evidence/elaborated-boundary.log). Pinned dependency objects were reused; this is not fresh Linux verification.

My [independent standard-library checker](statement-referee-2-evidence/independent-check.py) reconstructs both factor families and all 36 trace products for each, checks every positive-definiteness quadratic identity and leading-minor cross-check, and obtains det M=8192 and the coordinate determinants 32 and −32. It independently constructs the congruence coordinate matrix from its action on each symmetric basis matrix. Sparse polynomial determinant expansion in all nine independent matrix-entry variables yields exactly `(det S)^4`, with **120 nonzero degree-twelve monomials**. Every collected term agrees with the submitted diagnostic. [Exact result](statement-referee-2-evidence/independent-check.json). These are symbolic identities and exact arithmetic, not sampled matrices, but they still require actual Lean proofs.

## Complete-target fidelity

`AllMinimalOrbitsConnected` retains every k≥3, positive p,q, real p×q M, entrywise nonnegativity, actual ordinary rank k(k+1)/2 and real PSD rank k. Natural-number division represents the integer dimension exactly since k(k+1) is even. The conclusion is actual connectedness of the entire quotient, not path connectedness or connectivity of selected representatives.

`FactorTuple` has independent row and column families. `IsFactorization` imposes actual `Matrix.PosSemidef` on **every** member and every trace constraint. In the pinned Mathlib this means Hermitian plus nonnegativity of all quadratic tests; over ℝ it is precisely symmetric positive semidefinite. Neither entrywise nonnegativity of factors, strict positive definiteness, equality of row and column families, nor normalization is imposed on the full space. The reflected witness's negative off-diagonal entries are correctly allowed.

`IsPSDRank` is `IsLeast` of the complete positive-integer feasible-size set. Thus `witness_minimal_rank` must prove both existence at size three and exclusion of every smaller positive size. The dossier's flattened arbitrary-matrix trace factorization bound rank M≤k² is sufficient here: sizes one and two cannot have ordinary rank six. It is a legitimate simpler internal proof, without weakening the minimum claim or assuming the source's stronger general symmetric-dimension bound.

The literal strictly positive integer 6×6 M has the exact source entries. `witness_data` retains det M, actual Matrix.rank and both orientations. `witness_factorizations` includes both complete trace tuples and strict positive definiteness of all displayed factors. The full factorization space itself remains PSD, so singular individual factors in other factorizations are included in the quantified orientation theorem.

## Genuine orbits and quotient topology

`Congruent F G` quantifies over a single unit S of the full real square-matrix ring, with the actual inverse. This represents every invertible real change of basis, with either determinant sign. Both transformations have the exact canonical order: Sᵀ A S and S⁻¹ B S⁻ᵀ. No orthogonal-group, positive-determinant or rational restriction has been introduced.

The factorization subtype inherits the finite real product topology, hence the required Euclidean subspace topology. I inspected the pinned topology construction: `Quot r` carries the topology coinduced by `Quot.mk r`. Since `Quot` initially quotients by the generated equivalence relation, the public `orbit_semantics` theorem correctly requires the crucial additional equivalence

`Quot.mk Congruent F = Quot.mk Congruent G ↔ Congruent F G`.

This prevents silent enlargement of the canonical orbits. Reflexivity, inverse symmetry and composition with the correct order must establish that bridge. The first conjunct also explicitly asserts the canonical projection is a quotient map. No Hausdorff or other separation property of the quotient is assumed.

## Orientation and actual disconnectedness

For all actual size-three factorizations, symmetry gives the trace-coordinate identity M=U_A G U_Bᵀ with G=diag(1,1,1,2,2,2). The actual nonzero determinant of M forces U_A nonsingular throughout the **whole** fiber. Thus `orientation_nonvanishing` is appropriate and nonvacuous; it is not restricted to the two witnesses or to positive definite factors.

The symbolic congruence identity has the correct row-coordinate convention, and the fourth power is positive for any invertible real S, even with negative determinant. `orientation_preserved` quantifies over every actual pair and congruence. It cannot be discharged by checking only the two displayed tuples or a list of test transformations.

`quotient_separation` demands a continuous **surjection** from the entire genuine quotient to standard **discrete Bool**. The two opposite determinant signs provide the intended two values. Nonvanishing makes the sign locally constant; invariance permits descent by the quotient topology. A continuous surjection from a connected space to discrete Bool is impossible. The resulting `witness_disconnected` is therefore the intended topological claim, stronger than failure of a proposed interpolation or mere inequivalence of the two witnesses.

The final `canonical_counterexample` negates the full universal connectedness statement. One valid example at k=3,p=q=6 suffices. It does not replace the universal problem with a k=3-only conjecture. The manuscript's further constructions for every k and positive rational perturbations remain preserved but are not claimed by these exports; that distinction must remain explicit in eventual metadata.

## Numerical, API and review disposition

The dossier's positive-definiteness identities cover both signs and all factors, with positivity for every nonzero real vector. The symbolic congruence certificate is truly universal in all nine entries; it includes singular S even though sign invariance later uses invertibility. All exact integers and orientations match the complete source.

The proposed `0 < (32 : ℝ)` LeanCert kernel certificate is appropriate only when genuinely consumed with the actual orientation determinant theorem in the separator proof, as the final dossier now specifies. A successful numerical certificate alone will not discharge any topology or factor-space obligation.

Pinned Mathlib already supplies true PSD/congruence APIs, rank-product bounds, determinants, coordinate continuity, quotient-map descent and connected-image facts. The local definitions express the actual problem and contain no desired conclusion as an assumption. The specialized size-three determinant identity avoids unnecessary general representation theory; the public orbit semantics remains dimension-general.

My preliminary review identified one documentation mismatch: §8 named ten provisional exports despite nine actual Challenge declarations. The final reviewed dossier now lists the exact nine names, includes Bool semantics, and states the remaining internal bridges explicitly. This finding is resolved at the recorded hash. No substantive statement finding remains open.

The fixed ID/path and original source attribution are retained. New Lean headers credit George Stepaniants with the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, disclose substantial AI assistance, and preserve Matthew J. Colbrook's original counterexample attribution. No new contact email is added.

**APPROVE for the pre-proof freeze.** Proof implementation, independent final proof reviews, actual kernel/axiom checks, Lean4 Comparator, isolated Linux reproducibility and truthful publication-stage metadata are still required. This report establishes none of those future gates, and canonical status must remain **Solved** for now.
