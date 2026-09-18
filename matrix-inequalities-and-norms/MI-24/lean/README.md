# MI-24: the full Schatten norm complement in Lean

**George Stepaniants**  
Department of Computing and Mathematical Sciences, California Institute of Technology

This development proves the unchanged MI-24 target for every complex positive
definite pair `A, B`, every dimension `n >= 1`, every real finite `p >= 1`, and
the infinity endpoint. With the original ordered definitions

```math
G=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2},\qquad
L=A^{1/2}(B^{1/2}A^{-1}B^{1/2})^{1/2}A^{1/2},
```

the conclusion is

```math
\|A+B+G+L\|_p\le\|A+B+2L\|_p.
```

The finite norm is the actual trace-of-modulus Schatten formula. Separate
semantics theorems identify it with the singular-value formula and identify the
infinity norm with the largest singular value. No commutativity, symmetry of
`L(A,B)`, Heron inequality, norm axioms or desired conclusion is added as a premise.
The canonical problem ID, page and mathematical target are retained.

## Current verification status

**Complete immutable proof verification passed.** All 22 contracts passed actual local Lean332, two independent full-source reviews, and [non-root Linux run 35310937025](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35310937025/job/105492723099) at proof commit `97ff57c89775783bb7ebe952315840be86733417`. The [Linux evidence](verification/linux-2026-09-18/README.md) retains the artifact and logs. Final publication and PR merge checks remain separate; campaign acceptance is pending those checks.

| Check | Actual status |
|---|---|
| Statements before proof | The three frozen inputs and 22 contracts received two independent statement approvals before implementation; local289 freeze retained. |
| Local Lean | Actual local332 passed all 22 contracts in the full 34-module closure: 8 fresh compilations and 26 source/dependency/output-matched successful reuses. Root retained commands, hashes, logs and source snapshots. |
| Local matching and certificate use | Actual local333 independently elaborated Challenge and Solution; all 22 normalized types and universe lists matched. Proof-body traversal reaches both LeanCert checked bounds from the final theorem. This diagnostic is not Comparator. |
| Full source review | Baseline local325 reviews reported mathematical approval and requested library reuse/comment changes. The cleanup passes local332, and both independent exact-source continuation reviews approve. All four historical/current reports are retained in [the review index](reviews/INDEX.json). |
| Linux Comparator, default-kernel replay, sandbox and controls | Actual run 35310937025 passed at proof commit `97ff57c89775783bb7ebe952315840be86733417`; 22 exports and all per-project controls checked. |
| Staged packaging metadata | `Solution` is the default Lake target and the manifest root name is corrected to `NLAMI24`. Both metadata edits were included in the successful standalone Linux run; dependency pins and proof bytes match the reviewed local sources. |

[STATE.json](STATE.json) records the scope, hashes and remaining gates.
[IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json) maps every frozen contract to
its exact local332 proof source. There are no unresolved proof sorries. The 22
intentional `Challenge.lean` placeholders are specifications, excluded from
that count and from the proof dependency closure. Historical preproof comments
in frozen files remain unchanged; they do not override these current records.
Every exported proof used only `propext`, `Classical.choice` and `Quot.sound`
in the actual local checks.

## Read and reproduce

Start with [Definitions.lean](NLA/MI24/Definitions.lean), then the 22 contracts in
[Challenge.lean](Challenge.lean), and finish with
[Complement.lean](NLA/MI24/Complement.lean). [Solution.lean](Solution.lean) imports
the real proofs and requests an axiom report and kernel-trust check for all 22
exports; it does not import Challenge. The map gives the intermediate sources.

After installing the pinned Lean toolchain and dependencies, run from this
problem's `lean` directory:

```bash
lake build Solution
```

This is the proof target. A new local build establishes local Lean success,
which is distinct from the repository's final sandboxed checker.

For the complete checker on a supported **non-root Linux** environment, run from
the repository root, using the pinned repository harness:

```bash
tools/lean/bootstrap.sh /tmp/nla-mi24-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-24/lean /tmp/nla-mi24-tools
```

The harness needs its documented Linux dependencies and namespace/sandbox
support. It verifies committed source identity, builds in a fresh project copy,
runs the sandbox probe, kernel-replay regression controls, Comparator negative
controls and real 22-export comparison with the default kernel. An ordinary
macOS `lake build` does not establish these Linux results. These commands reproduce the class of check actually completed at the immutable proof revision above.

The pins are Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The exact checker source-lock and
pattern/standard hashes are listed in
[SOURCE-ATTRIBUTION.json](SOURCE-ATTRIBUTION.json).

## What the proof establishes internally

The proof derives the needed `q=2`, `0<=r<=1` Furuta inequality, geometric-mean
congruence and fixed point, the full weighted trace comparison, and the Heron
inequality for all real `p>=1`. These results are proved within Lean, not assumed
from their papers. Actual minors/exterior powers and a proved scalar
prefix-product-to-sum lemma supply the trace bridge. Singular PSD matrices,
scalar zero, `p=1`, and compound degree zero are covered by the relevant helpers.
The infinity endpoint follows from explicit finite-power trace bounds.

George's convexity deduction completes the proof: the middle matrix is the
average of the Heron and right endpoints; Heron plus the proved Lin comparison
bounds the first endpoint by the middle, and the triangle inequality gives the
required comparison with the other endpoint.

Only two affine scalar bounds are delegated to LeanCert, on the single interval
`0 <= u <= 1/2`. Both use `trust := kernel`; neither requires matrix-entry
sampling, numerical eigenvalues, nor interval subdivision. Their actual proof
bodies are consumed by the trace Young argument and ultimately the final theorem.

## Sources, review and authorship

The original conjecture and ordered Lin formula are due to
[Ghabries, Abbas, Mourad and Assi](https://arxiv.org/html/2105.13356v1#S4).
The Heron comparison is due to
[Dinh, Dumitru and Franco](https://doi.org/10.1016/j.laa.2017.06.040).
The internal Furuta proof follows the bounded route explained by
[Fujii](https://emis.muni.cz/journals/AFA/AFA-tex_v1_n2_a4.pdf).
George Stepaniants is credited for the complete convexity deduction; its
[canonical source](source-inputs/canonical/solution.md) and original target are
retained. Prior mathematical authorship is preserved. No source-author
endorsement or external human peer review is inferred.

The code was prepared with substantial Codex assistance: agent
`/root/nm04_final_referee1` wrote the principal development; `/root` wrote the
scalar prefix-product transfer; `/root/mf06_final_referee2` contributed the
review-requested reuse and explanatory-comment cleanup. These contributors do
not provide independent final code verdicts. Historical pre-implementation
statement reviews are recorded separately. Nonauthor reviewers apply the pinned
Tau Ceti correctness, generality, proof-quality, attribution and reuse rubrics;
this is not an execution of a Tau Ceti review service.

The Schiffer and Forsythe developments supplied inspected statement/reproduction
patterns; accepted MI21/MI22 and MF05/MF06 sources supplied the attributed API,
certificate and exterior-power patterns. Mathlib and LeanCert receive their
original code credits. Source URLs, immutable pins and reviewed payload hashes
are retained, without redistributing full third-party paper PDFs or extracted
texts whose redistribution permission has not been established.

The recorded public duplicate audit inspected 15 repositories, 269 public branch
heads and 223 unique commits, replacing truncated API trees with complete Git
trees. It found no target-named MI-24 formalization in that scope. This was a
path/ID search of the observed public upstream/direct-fork branches; it does
not establish PR coverage or a semantic search of unrelated files or
private/unpublished work.
It does not certify historical priority. Standalone package validation and the immutable proof-commit Linux run passed. The two source-bound nonauthor approvals are complete; later publication and PR merge checkouts remain separate gates.

The [coordinator publication preflight](verification/MI24-ROOT-PACKAGE-PREFLIGHT.json) checks the complete package, current upstream source correspondence, dependency pins and privacy. It preceded the actual Linux execution and is separate from the two independent full mathematical/source reviews.
