# MI-13 — independent rectangular operator-norm proof review

**Mathematical fidelity and retained local evidence: PASS. Request the bounded proof-quality changes below before final source acceptance.** This review covers exactly one frozen contract, `NLA.MI13.operator_norm_semantics`. It does not accept the complete MI-13 target or establish a new Lean, Comparator, kernel-replay or sandbox run. The count change is zero.

Reviewer: `/root/sf_ra_runtime_referee`. I authored none of the scoped definitions, statements, proof, author handoff or compiler records. I independently read the entire 103-line `OperatorNorm.lean`, the entire unchanged 109-line Definitions and 37-line SingularSemantics dependencies, and the complete author proof plan and API handoff. I also read the 41-line GramBasis module as contextual API comparison; it is not imported here and its contracts are not new approvals in this review. I wrote only this private review directory and invoked no compiler, Lake, Git, network, proof-source edit, publication or counting operation.

## Exact statement and source boundary

The reviewed source is `next-proofs/MI-13/NLA/MI13/OperatorNorm.lean`, SHA-256 `14db6e512d1a7bd07f8fd710d5570d61ad8fa2191d9328effce411e5c5755e36`. Its complete theorem header is byte-identical to the frozen Challenge and the author snapshot:

```lean
theorem operator_norm_semantics {m n : ℕ} (A : Rect m n) :
    spectralNorm A = singularValue A 0 ∧
    (spectralNorm A = 0 ↔ A = 0) ∧
    ∀ x : EuclideanVector n, ‖euclideanCLM A x‖ ≤ spectralNorm A * ‖x‖ := by
```

`EXACT-HEADER.json` binds that header, including its complete quantifiers and conjunction. All thirteen frozen inputs remain unchanged, including all thirty-six Challenge contracts and the complete Comparator name list. The root's separate acceptance record precedes this proof run; the older freeze's historical pending wording was preserved. The author's sealed packet truthfully describes an unrun candidate at its preparation time. The later actual local34 evidence is recorded separately here.

The retained canonical MI-13 page has SHA-256 `20a8326f71cf7eba180b3cb956cc7c374298823ceb6aae8be72489d49c86f730`, from commit `ebdf2f34dc7690d8e323faaeb40d6dcc30c851ff`, canonical path `matrix-inequalities-and-norms/MI-13/README.md`. Its recorded literal Git blob identity was recomputed without invoking Git. The full original target remains the coefficient-two inequality for `ABC − CBA`, all complex rectangular `A,C : Rect m n`, `B : Rect n m`, and `m,n ≥ 2`. The current theorem supplies its norm/singular-value semantic bridge, with the stronger helper scope of every natural `m,n`; it proves none of the remaining inequality steps by itself.

The unchanged canonical page, full Challenge, source correspondence and pre-code numerical/contract plan were read in my earlier sealed fifteen-contract prefix review. Their exact bytes were reauthenticated here. That earlier review's complete 98-file payload inventory is authenticated, and its exact Definitions/SingularSemantics source hashes match the present dependencies. This is scoped continuation of my own earlier review, not a second independent reviewer or a fresh approval of the other prefix modules, some of which now have separate cleanup changes.

## Mathematical assessment

The definitions are genuine: `euclideanLin A` is the matrix's actual map between complex Euclidean spaces; `euclideanCLM A` is its finite-dimensional continuous-linear realization with the same action; `spectralNorm` is that map's actual operator norm; and `singularValue` is Mathlib's decreasing, nonnegative, multiplicity-preserving, zero-extended singular-value sequence. No desired norm or spectral identity is assigned by definition. Only SingularSemantics is imported from the project, and its nonnegativity, antitonicity and zero-extension conclusions are all consumed. Challenge, SVD, GramBasis, padding and subsequent MI-13 contracts are not dependencies.

The proof takes the ordered orthonormal eigenbasis of the genuine Gram map `A* A` on the domain. The dimension witness is the actual `finrank_euclideanSpace_fin`. `eigenvectorBasis_apply_self_apply` expresses the Gram map diagonally in that basis, and `sq_singularValues_fin` identifies each eigenvalue with the corresponding singular-value square. The explicit RCLike-to-Complex and real-power cast rewrites preserve the same scalar; no complex order or real-entry assumption is introduced.

The energy identity is

`‖A x‖² = Σ i, singularValue A i.val² * ‖b.repr x i‖²`.

The adjoint identity changes the image self-inner-product to the Gram quadratic form, and the basis representation preserves the complex inner product. Expanding the Euclidean inner product and taking real parts is legitimate for the finite sum. Scalar linearity is used in the **second** inner-product argument, so its orientation respects conjugate linearity in the first. The scalar squared singular value and squared coordinate norm are real; their explicit complex casts therefore have the stated real product. There is no missing conjugation or replacement of arbitrary complex coordinates by real coordinates.

For the upper bound, every in-range singular value is nonnegative and at most the zeroth value. Thus its square is bounded by the zeroth square, and multiplying by the nonnegative coordinate norm square preserves order. Parseval is the actual Euclidean squared-norm identity followed by the basis isometry. The passage back from squares supplies both nonnegativity premises explicitly. `opNorm_le_bound` applies to the resulting bound on **every** domain vector and to a nonnegative proposed constant; the operator norm is not inferred from an unjustified maximum or a sampled vector set.

For the reverse bound when `n > 0`, the chosen `Fin n` index is exactly zero and is justified by `Nat.pos_of_ne_zero`. The representation of its basis vector is the actual Euclidean single with value one. The finite sum in the energy identity therefore collapses to the zeroth singular-value square. Both sides are nonnegative, so equality of squares gives equality of norms. This vector has norm one and supplies the lower bound through `le_opNorm`. Repeated singular values and deficient rank pose no issue; the proof selects an ordered eigenbasis without uniqueness or strict positivity assumptions.

For `n = 0`, no unit vector or index is chosen. Zero extension gives `singularValue A 0 = 0`, and nonnegativity of the operator norm supplies the reverse inequality. The upper argument already covers the empty sum. For `m = 0` and `n > 0`, the codomain is trivial but the Gram construction and chosen domain basis remain valid; the energy identity yields zero image norm and hence a zero first singular value. The unique empty rectangular matrices, the zero matrix, both dimension orderings, rank zero, rank deficiency and repeated spectra are all included. The proof never divides by a singular value.

The zero-norm equivalence first uses definiteness of the actual CLM norm. The finite-dimensional linear-to-continuous-linear equivalence and matrix-to-Euclidean-linear equivalence are injective and preserve zero, including empty index types, so a zero map implies the zero matrix. The converse follows from the same zero-preservation. The final application inequality is the standard operator-norm inequality for that identical CLM. No injectivity of `A` is assumed.

There is no additional numerical certificate or interval computation in this module. All reasoning is symbolic. The positive-half certificate belongs to the separate averaging argument; importing or rerunning it here would add no mathematical support.

## Actual local evidence and reuse

The independent static/evidence audit passed **1,404 checks with 242 external bindings**, rechecked at the end. It authenticates all fourteen author-packet payloads, the exact active/shared/snapshot source, the frozen header, all thirteen immutable inputs, the prior review inventory, and twelve selected pinned primary files. These checks authenticate records and bytes; the mathematical assessment above comes from direct source reading.

I read the complete actual local34 log. Its sole line reports exactly `[propext, Classical.choice, Quot.sound]` for `NLA.MI13.operator_norm_semantics`; there are no warnings or errors. The exact source includes `#print axioms` and `#assert_trust kernel`, and the authenticated actual command exits zero. The output SHA-256 is `85707b9a5b730d01c2570900ef15584ea8d9a07e829dbf4ed88421bf3d47ea0d`; the log SHA-256 is `eb322ec4b1de4dac01215ae598656bb8208ccaebbee596e7173919ddee344f30`.

The actual invocation uses Lean 4.33.1 with `--threads=1 --memory=4096`, in the shared macOS workspace, from `2026-09-17T05:16:10.251689+00:00` to `05:16:32.656830+00:00`. Its receipt and full assembly match. Assembly34 adds only OperatorNorm to assembly33 and retains every prior source record. The selected module order is exactly Definitions, SingularSemantics, OperatorNorm; the first two are authenticated reuse and only the final module is freshly compiled in that run. All three complete successfully, with no failed or blocked module. This is an actual root-coordinated local run, not execution by this reviewer and not GitHub Comparator.

`REUSE-CHAINS.json` independently traces 25 command/reuse nodes back to actual successful origins: Definitions in local20, SingularSemantics in local21, and OperatorNorm in local34. Every link checks the prior receipt digest, unchanged complete project-source closure, output hash and ordering. Fresh origin commands also bind the immediate project dependency outputs. The complete actual origin logs for Definitions and SingularSemantics were read; the former is empty and the latter has exactly its two standard-three-axiom reports. Current retained output bytes match all three successful origins and private evidence copies are retained. A failed unrelated command in an earlier receipt is not treated as a successful whole run or reused as a theorem output.

The full receipt/assembly inventories and their chain from local20 through local34 were authenticated. This does not approve unrelated modules contained in those inventories. The retained compiler binary and serial runner hashes match the records. The runner uses a compiler lock, sequential subprocesses and a one-thread setting; the recorded run intervals do not overlap. This establishes the recorded execution design and chronology, not a separate historical census of all machine processes. The older initial environment record's 2048 MiB text is historical; the actual runner, assembly and command for this task expressly use 4096 MiB. The receipt's cumulative child-resource field is not relabeled as a new independently measured peak.

All ten project/local dependency records and retained package HEAD files match their pins, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Twelve selected Mathlib snapshots match current source bytes and their retained author provenance; eight use inherited literal-commit comparisons and four have the author's newly retained comparison records. I performed no fresh network request. Direct imported external source/cache digests are observed now; they were not all measured contemporaneously in the original compiler receipt. No fresh external-cache rebuild or kernel replay is claimed.

The audit's first attempt wrongly omitted nested files named `MANIFEST.json` from the prior review's payload inventory. Its corrected check excludes only the top-level manifest and passes with no missing or extra payload. Both audit-reader versions/logs are retained. No Lean source or compiler repair occurred in this review.

## Required proof-quality continuation

The pinned Tau Ceti guidance and its correctness, generality, proof-quality, reuse and attribution rubrics were read in my prior review and their exact bytes reauthenticated here. I reread the proof-quality rubric in this task. The applicable pin remains `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. The pinned Comparator guidance is likewise byte-identical to the copy already fully read. This is an independent AI-agent review using those standards, not an official Tau Ceti service or human peer review.

The proof-quality rubric requires explanations for representation-changing `change` steps and internal structure in a long proof. Please make this bounded cleanup without altering the statement:

1. At lines 54–55, explain that multiplication of complex scalars is exposed as the scalar action on `ℂ` so `inner_smul_right` applies. Prefer an explicit scalar-action rewrite if suitable; this step must not silently rely on an unexplained representation change.
2. At line 60, expose `spectralNorm` with its defining rewrite, or explain why the `change` is needed to reach the CLM norm interface.
3. At line 65, explain the equality of the CLM and linear-map actions, or use the available `LinearMap.coe_toContinuousLinearMap'` API with the project definition. The action is mathematically identical, but the coercion/definition bridge should be visible.
4. Add brief internal comments separating the Gram-coordinate energy identity, the universal upper bound, the zero/nonzero-domain lower bound, and the final zero-map equivalence. The local energy helper is a coherent one-off in this proof; factoring it into a named lemma is another acceptable option, not a requirement to invent a new public API.

The exact basis-coordinate simplification at line 83 has been independently checked against `OrthonormalBasis.repr_self`, `PiLp.single_apply` and the finite sum; the requested lower-bound explanation should make that reason visible. I found no unused simp warning in the actual successful log and request no arbitrary tactic rewrite. The proof already reuses the actual spectral, singular-value, basis, adjoint and norm APIs; it does not reconstruct those foundations. A bounded search in Mathlib's InnerProductSpace directory found norm-determinant/singular-value product results, not an operator-norm identity under that spelling. This is a targeted reuse check, not a global absence theorem.

These changes concern proof maintenance and readability, not correctness or the frozen mathematical statement. Root should retain the exact cleanup diff, obtain source-matched local success for the changed module and any affected outputs, and request bounded continuation review. This report does not approve unseen corrected bytes.

George Stepaniants retains the Department of Computing and Mathematical Sciences, California Institute of Technology credit, with substantial Codex assistance disclosed. Nobori's original question, Audenaert's refined commutator theorem and the repository reduction retain their mathematical attribution. No contact address is included.

All other new MI-13 modules, complete-target acceptance, completed-project metadata, publication, counting, and final non-root Linux Comparator/default-kernel/sandbox controls remain outside this bounded review.
