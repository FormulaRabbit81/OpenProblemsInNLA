# MI-04 Lean formalization

This candidate targets the full original implication. For every integer $n\ge1$ and every complex $n\times n$ matrix $X$, suppose **every** Hermitian pair $A,B$ with

$$\begin{pmatrix}A&X\\X^*&B\end{pmatrix}\succeq0$$

satisfies the stated Euclidean operator-norm bound. Then there are an actual Hermitian matrix $K$ and complex scalars $\alpha,\beta$ such that $X=\alpha K+\beta I_n$. Singular completions, zero and scalar matrices, repeated values, and dimensions one and two remain included. The manuscript’s converse and four-way equivalence are outside this formal claim.

**Local Lean build passed; canonical verification pending.** The exact 21-file implementation graph and all 21 frozen exports passed the coordinator’s serial macOS development build, completed on 16 September 2026 at 20:32:23 UTC. Eighteen exact successful outputs were reused through source-bound receipts; the corrected diagonalization and final two modules compiled in development06. The final entrypoint printed only `propext`, `Classical.choice` and `Quot.sound` and passed its kernel-trust assertions. [Actual local evidence](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) retains every command origin and the stated limitations. This is not a Linux sandbox, fresh default-kernel replay, Comparator or rejection-control result. No published proof commit or verification count is claimed.

Read [the numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/MI04/Definitions.lean), [Challenge](Challenge.lean) and [source correspondence](SourceCorrespondence.md) first. These frozen files retain their original preparation-phase wording as historical evidence; [the statement freeze](STATEMENT-FREEZE.json) and separate implementation authorization document the transition to proof work. [Conclusion](NLA/MI04/Conclusion.lean) states the explicit original implication. [Solution](Solution.lean) imports the complete implementation and asserts kernel trust for all 21 exports; it never imports Challenge. The 21 deliberate Challenge placeholders are specification obligations, not accepted proofs.

The proof uses an attained Rayleigh maximum and an exact second-order sandwich: one explicit test vector gives the lower bound, and weighted-square inequalities bound **every** unit vector from above. Two rational diagonal probes give off-diagonal magnitude symmetry. Orthonormal-basis extension and Parseval then prove normality. The Hermitian real and imaginary parts provide a finite joint-eigenspace decomposition and a full unitary eigenbasis, without dividing by an eigenvalue or assuming simple spectrum. A three-coordinate orthogonal pair detects collinearity; real affine coordinates reconstruct the Hermitian matrix.

All dimension-dependent sums remain symbolic. The LeanCert numerical certificate is the exact constant bound **$0<1/4$**, proved with `interval_decide (trust := kernel)` in [UpperBound](NLA/MI04/UpperBound.lean). It is explicitly consumed in both denominator-positivity arguments needed by the universal upper bound. There is no variable interval search, eigenvalue approximation or subdivision. Every export has a LeanCert kernel-trust assertion. [comparator.json](comparator.json) lists the exact 21 declarations, permits no definition holes, and allows only `propext`, `Classical.choice` and `Quot.sound`; these are both the acceptance limits and the measured local axiom sets. Canonical checking must verify them again.

With the pinned dependencies available, run `lake build` from this directory to build Solution. The sole [configuration amendment](verification/packaging/TRANSITION.json) changes the active default from Challenge to Solution; the original frozen Lakefile and all ten frozen snapshots remain byte-identical. `Solution.lean` contains exactly the bytes tested locally as `NLA/MI04/Complete.lean`. The fresh canonical build must test this packaging as well.

From a fresh committed repository, the authoritative check uses the unchanged shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-04/lean /absolute/path/to/nla-lean-tools
```

The supported non-root Linux sandbox, actual source hashes, default-kernel replay, Comparator results and problem-specific rejection controls are separate requirements. A successful development build, metadata-schema validation or agent review is insufficient. [Publication evidence](PUBLICATION-EVIDENCE.json) records the present source and review state; unobserved evidence slots stay empty.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. Original mathematical proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Bourin and Lee retain credit for the conjecture. Substantial OpenAI Codex assistance is disclosed. The [review protocol](../../../docs/lean/REVIEW.md) adapts Tau Ceti standards without claiming its endorsement or human peer review. Schiffer and Forsythe informed the structure; Mathlib, LeanCert and Lean Comparator provide the pinned foundations and tools. [Source and repair reviews](reviews/INDEX.json) retain their exact historical scopes. The package preparer authored later repairs and is not counted as their referee. Original contact-bearing source wrappers are omitted from this new archive with immutable source hashes and links in [the omission record](verification/OMITTED-ORIGINALS.json). No contact email is supplied. License: [Apache 2.0](LICENSE).
