# MI-13 — second independent review of the fifteen-contract prefix

**Approve the mathematical fidelity and authenticated local evidence for the exact prefix below. Request the bounded proof-quality cleanup listed below before final source acceptance.** This is a conditional prefix review, not approval of the complete MI-13 target, a fresh Lean run, or GitHub Comparator acceptance. The count change is zero.

Reviewer: `/root/sf_ra_runtime_referee`. I authored none of these definitions, statements, proofs, compiler records or earlier MI-13 reviews. I independently read every line of the seven scoped files, including all helper proofs, before consulting the first prefix referee's findings. The coordinator subsequently reported that referee's two undocumented representation changes and two unused simp arguments; my own reading and the actual local log confirm them. I did not rely on that other prefix review as proof evidence. I wrote only this private review directory and invoked no compiler, Lake, Git, network, publication or counting operation.

## Exact scope and original target

The scope is all **507 lines in seven files**, with **fifteen of the thirty-six frozen contracts**. Complete hashes, headers and import closures are in `SOURCE-MAP.json`, `HEADERS.json` and `IMPORTS.json`; exact source copies are retained under `evidence/current-source`.

| Module | Lines | Frozen contracts reviewed | Successful local origin |
| --- | ---: | --- | --- |
| Definitions | 109 | Concrete semantic definitions; no theorem export | development-20 |
| Numerical | 27 | half_certificate | development-21 |
| SingularSemantics | 37 | singular_values_semantics; singular_values_gram | development-21 |
| GramBasis | 41 | ordered_gram_basis; positive_image_extension | development-25 |
| Frobenius | 118 | frobenius_semantics; frobenius_linear_bounds; hilbert_schmidt_semantics | development-24 |
| ElementaryBounds | 92 | two_coordinate_bound; off_corner_coefficient_bound; unit_circle_lift; frobenius_average_bound | development-26 |
| NormalizedImages | 83 | positive_image_orthonormal; zero_singular_image; full_singular_vector_bases | development-28 |

I read the full 126-line canonical page, all Definitions, all 219 lines and thirty-six complete Challenge contracts, source correspondence, numerical targets and numerical-first record, pre-code contract plan, finite route and obligations, freeze, README, state and review plan. I read both earlier independent statement reports and the local statement-elaboration audit. Their statement/runtime scopes remain distinct from this proof review. All thirteen frozen files retain their exact hashes; the separate root acceptance record authorizes proof development after the earlier reviews and actual local statement elaboration. The historical freeze's pending-acceptance wording was correctly retained rather than rewritten.

The original source is `matrix-inequalities-and-norms/MI-13/README.md` at retained upstream commit `ebdf2f34dc7690d8e323faaeb40d6dcc30c851ff`, SHA-256 `20a8326f71cf7eba180b3cb956cc7c374298823ceb6aae8be72489d49c86f730`. Its bytes reproduce the recorded literal Git blob identity. The complete frozen target is precisely

`F(ABC − CBA)^2 ≤ 2 O(B)^2 (sv(A,0)^2 + sv(A,1)^2) F(C)^2`

for all natural `m,n ≥ 2`, every complex `m × n` pair `A,C`, and every `n × m` matrix `B`. It retains every rank, both dimension orderings and coefficient two. No invertibility, nonzero, distinct-spectrum, real-entry or supplied-SVD assumption enters that target. This prefix has not proved it. The other twenty-one contracts are outside this proof approval, including operator-norm semantics, the matrix SVD, unitary invariances, commutator adjoint/J/spectral facts, the refined estimate, two-unitary averaging, middle-factor reductions, padding and sharpness. The newly added SVD module and local run 29 were explicitly excluded; this is not an assertion that every excluded contract remains unimplemented.

## Independent mathematical assessment

The definitions use genuine objects. `frobeniusNorm` is the norm of every entry flattened into complex Euclidean space; `spectralNorm` is the actual Euclidean CLM operator norm. `singularValue` is Mathlib's decreasing, nonnegative, zero-extended singular-value sequence of the same Euclidean linear map. Gram eigenvalues come from its actual adjoint composition and ordered spectral theorem. Neither norm is a convenient default matrix norm, and no spectral value or required inequality is assigned by definition. I checked the relevant pinned Euclidean, norm, inner-product, adjoint, ordered-spectrum and singular-value API excerpts. The separate operator-norm/first-singular-value identity remains outside this prefix.

`SingularSemantics` directly uses the existing nonnegativity, antitonicity, zero-extension and squared-singular-value theorems, with the actual finite Euclidean dimension. `GramBasis` constructs the ordered orthonormal eigenbasis and converts the squared real singular value to its complex scalar correctly. Its explicit `RCLike.ofReal_eq_complex_ofReal` and `Complex.ofReal_pow` rewrites address the recorded casting failures without changing a hypothesis or conclusion. Repeated and zero singular values require no distinctness assumption.

The normalized-image proofs respect conjugate linearity in the first inner-product argument. The adjoint identity gives `<Av_i,Av_j> = s_j² <v_i,v_j>`. On positive indices, both inverse factors are legitimate; complex conjugation fixes their real scalars. Off-diagonal orthogonality uses injectivity of the subtype projection, and the diagonal proof uses the strictly positive singular value to justify cancellation. For a zero singular value, the self-inner-product is zero, hence the actual image is zero. Partial orthonormal extension then supplies a complete basis while fixing the positive indices. The final positive/nonpositive split reconstructs `Av_i = s_i u_i` at every index. The nonpositive branch uses established singular-value nonnegativity to obtain equality to zero. Empty square dimension, rank zero, deficient rank and multiplicities are preserved, with no global Nonempty instance or hidden rank hypothesis. `GramBasis` has an unrestricted constructed witness and real consumers; it is not an existence oracle.

The Frobenius helpers establish genuine entrywise linearity and injectivity of flattening, squared norm as the finite entry sum, and the real Gram trace identity. The complex inner product equals `tr(A* C)`, with the correct conjugation and sum order. Norm definiteness, complex scaling and triangle inequalities are inherited from that actual Euclidean norm. The explicit pair-index commutator coefficients give `XY − YX`: summing the first Kronecker term fixes the column, while the second fixes the row. The final scalar `mul_comm` exchanges complex entries only; it assumes no matrix commutativity. These identities remain valid in empty rectangular dimensions.

The two-coordinate estimate squares a nonnegative triangle bound and uses the nonnegative square `(s‖q‖ − t‖p‖)²`; the real-to-complex norm casts use exactly the stated nonnegative hypotheses. The off-corner estimate separates `i=0` from `i≥1`, forcing the other index to be at least one in the former case, and squares inequalities only for nonnegative values. The unit-circle proof uses `sqrt(1−d²)²=1−d²` on the whole closed interval `[0,1]`, including both endpoints, and proves the average algebraically.

The averaging proof genuinely consumes `half_certificate.1`: its resulting `hhalf` is passed to the multiplication inequality and the nonnegativity premise used when squaring that inequality. It is not an unused imported certificate. The exact equality of two halves is proved symbolically. There is one explicit `interval_decide (trust := kernel)` invocation at a closed scalar input, no source-level interval subdivision, spectrum approximation, matrix enumeration or increased resource option. The retained output reports theorem axioms, not the tactic's internal precision/refinement trace; I do not claim to have measured a least precision or an internal solver event separately. All variable matrix and scalar inequalities here are symbolic.

## Local evidence and successful-output reuse

The independent read-only Python audit passed **1,827 checks with 361 resolved external bindings**. It authenticates the seven current sources against their original successful source hashes, all fifteen complete frozen headers, thirteen frozen inputs, all thirty-six Comparator names, the three prerequisite review inventories, and all 292 external bindings of the earlier statement-elaboration audit. It rechecks every bound input at the end. This is evidence authentication, not a new proof-checking execution.

The full actual logs for Definitions, Numerical, SingularSemantics, GramBasis, Frobenius, ElementaryBounds and NormalizedImages were read. Definitions' successful log is empty. The fifteen successful theorem reports each contain exactly `propext`, `Classical.choice` and `Quot.sound`, and the corresponding source has an explicit `#assert_trust kernel`. The only successful-run warnings are the two Frobenius unused simp arguments noted below. There are no successful-log admitted axioms or errors.

All nine receipts and assemblies from development-20 through development-28 were authenticated. Their full source inventories agree, the assembly chain is intact, and the literal command vectors use Lean 4.33.1 with `--threads=1 --memory=4096` in the shared macOS local directory. The retained runner has an advisory compiler lock, sequential subprocess calls and one-thread environment setting; recorded command/run intervals do not overlap. This does not establish an independent historical census of every process on the machine. The compiler and runner hashes are recorded in the receipts and rechecked. Root's freeze acceptance precedes the first proof run.

`REUSE-CHAINS.json` traces 24 successful command/reuse nodes recursively back to actual successful invocations, checking the prior receipt digest, source closure, output digest and immediate dependency outputs. A receipt containing a failed unrelated module is not treated as wholly successful: only its individually authenticated successful/reused commands are usable. No failed GramBasis or NormalizedImages output is reused as a success. Current retained output bytes match all seven successful origin digests, and private copies are evidence only.

The full unsuccessful GramBasis logs from runs 22 and 23 and the unsuccessful NormalizedImages log from run 27 were also read and retained. The latter leaves `1 = if True then 1 else 0`, then reports `sorryAx` and rejects the affected declarations through `#assert_trust`. The authenticated repair changes exactly `if_pos rfl` to `if_pos True.intro` in the proof body. All headers remain identical. Its after-source SHA-256 is `ca365a0c2f783736137682a840cde1a7d5723615dab6d60d630f805c7eb3fd2b`, and fresh run 28 succeeds with the standard three axioms for all three scoped declarations. The failure is not erased or relabeled as a success.

All ten project/local dependency records and retained package HEAD files match their pins: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Lean 4.33.1. All ten retained primary snapshots match their local source files. Direct imported external source/cache digests were observed now and recorded separately. Unlike project dependency outputs, those external cache digests were not all measured in the original compiler receipt; this review does not manufacture that historical binding or a fresh cache rebuild. Actual non-root Linux Comparator, default-kernel replay, sandbox and rejection controls remain required later.

The audit's first attempt failed because its header reader mistook the named argument `(m := r)` for a theorem proof boundary. The corrected reader stops at `:= by`; its next complete run passed. Both reader versions/logs are retained. This was an audit-reader error, not a Lean source or proof repair.

## Required cleanup and standards scope

I read the retained Tau Ceti guidance and correctness, generality, proof-quality, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. The Comparator guidance copy at `2312244ac716564a61cc0bf4e107d9abf1757a61` matches the full copy already read in my earlier runtime reviews. This is an independent AI-agent review applying the pinned guidance, not an official Tau Ceti service or human peer review.

The proof-quality rubric explicitly requests explanations for representation-changing `change` steps. Before final source acceptance:

1. Explain the Euclidean CLM/entry-coordinate expansion at `Frobenius.lean:87`, including which fixed wrappers are unfolded and why the chosen representation is needed; alternatively replace it with a suitable named API rewrite.
2. Explain the subtype/domRestrict projection at `NormalizedImages.lean:37`, or replace it with an explicit API rewrite.
3. Remove the unused `PiLp.toLp_apply` at `Frobenius.lean:53` and `ite_mul` at line 99, preserving the still-used occurrence at line 95. The actual successful log identifies exactly these two warnings.

These are documentation and proof-maintenance changes. They do not require a statement amendment. Root should record their exact diff, rerun the changed proof modules and affected dependencies locally, and obtain bounded source-continuation review. This review does not approve unseen cleanup bytes.

The substantive proofs reuse existing Mathlib spectral, singular-value, adjoint, norm and orthonormal-extension APIs. Targeted searches also locate the separate Matrix Frobenius norm instances; the current development instead needs the frozen explicit Euclidean flattening and Hilbert-space commutator interface, and its small bridges have actual consumers. I found no reimplemented spectral or rank-counting foundation. I performed targeted library searches and API reading, not an exhaustive absence claim over Mathlib or a new Tau Ceti implementation checkout.

George Stepaniants retains the Department of Computing and Mathematical Sciences, California Institute of Technology credit, with substantial Codex assistance disclosed. Nobori's original question, Audenaert's refined commutator theorem and the repository reduction retain their prior mathematical attribution. This review invents no individual authorship of the reduction or priority claim. No contact address is published.

Final approval of every proof module, the complete original inequality, truthful completed-project metadata, real GitHub Linux controls, exact published-source continuation and any verified-count decision remain separate later gates. Only the exact seven-file, fifteen-contract prefix is reviewed here.
