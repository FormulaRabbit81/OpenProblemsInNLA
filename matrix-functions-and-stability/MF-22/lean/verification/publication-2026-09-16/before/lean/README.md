# MF-22 Lean formalization

This candidate proves the full original polynomial-conditioning target with exponent **2**. For every fixed real $\rho>0$, it supplies $K_\rho>0$ and $n_0\ge1$ such that every $n\ge n_0$ has

$$\det H_n(\rho)\ne0,\qquad \kappa_2(H_n(\rho))\le K_\rho n^2.$$

Here $H_n(\rho)$ is the original complex $2n\times2n$ pure Toeplitz truncation, with the literal coefficient blocks and boundary conditions. The condition number uses the induced complex Euclidean operator norm; singular matrices have infinite condition number. The parameter $\rho=\sqrt{10}$ is included. The retained informal manuscript's stronger **linear** bound is not claimed as a formal result.

**Complete development build passed; canonical verification pending.** All 22 frozen exports and the full 29-file source closure passed actual non-root Linux development run 35052024095 at `93abf01922d103993f2a92e819f207d63effbfae`. Two independent agents approved the complete mathematical source. This standalone package still requires actual Comparator, default-kernel replay, transitive axiom/control checks and final source-bound referee reconciliation. No canonical status or verified count is changed by this package.

Start with [the numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/MF22/Definitions.lean) and [Challenge](Challenge.lean). The final implication is [polynomial_conditioning](NLA/MF22/Conditioning.lean); [Solution](Solution.lean) imports the complete graph and checks all 22 exports. [Source correspondence](SourceCorrespondence.md), [proof architecture](PROOF-ARCHITECTURE.md), [export locations](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml) and [evidence inventory](PUBLICATION-EVIDENCE.json) provide the audit trail.

The proof derives the exact four-state recurrence, classifies its roots, proves noncancellation and the actual finite inverse, and cancels the growing Green terms before bounding entries. Uniform inverse-entry bounds and dimension-times-entry estimates for both operator norms give the sufficient exponent 2. Fixed-size algebra and an exact completed square remove parameter interval searches. LeanCert certifies the remaining positive integer margin in kernel mode; every exported declaration has a kernel-trust assertion. No native-evaluation or additional-axiom acceptance is intended.

With the pinned toolchain and dependencies available, `lake build` now selects the complete Solution graph. The original statement-phase default is retained in the packaging record; changing this default changes no mathematical source or dependency pin. For authoritative verification from a fresh committed repository, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-22/lean /absolute/path/to/nla-lean-tools
```

These commands require the supported non-root Linux isolation environment. The shared verifier runs fresh problem-specific controls, Comparator and default-kernel replay; a development build or source review does not substitute for them. [comparator.json](comparator.json) lists all 22 targets, has no definition holes and allows only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The actual complete development axiom report uses only these standard axioms; the canonical run must independently check them again.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI assistance. Bogoya, Böttcher, Ferrari, Grudsky and Serra-Capizzano retain credit for the family, question and source root classification; George Stepaniants is separately credited for the retained manuscript. The [review protocol](../../../docs/lean/REVIEW.md) adapts Tau Ceti standards and does not claim Tau Ceti or human endorsement. Schiffer and Forsythe informed the organization; Mathlib, LeanCert and Lean Comparator supply the pinned foundations and checking tools. License: [Apache 2.0](LICENSE).
