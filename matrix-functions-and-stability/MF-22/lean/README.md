# MF-22 Lean formalization

This formalization proves the full original polynomial-conditioning target with exponent **2**. For every fixed real $\rho>0$, it supplies $K_\rho>0$ and $n_0\ge1$ such that every $n\ge n_0$ has

$$\det H_n(\rho)\ne0,\qquad \kappa_2(H_n(\rho))\le K_\rho n^2.$$

Here $H_n(\rho)$ is the original complex $2n\times2n$ pure Toeplitz truncation, with the literal coefficient blocks and boundary conditions. The condition number uses the induced complex Euclidean operator norm; singular matrices have infinite condition number. The parameter $\rho=\sqrt{10}$ is included. The retained informal manuscript's stronger **linear** bound is not claimed as a formal result.

**All 22 targets passed canonical Linux verification.**
[Run 35053254275](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35053254275/job/104658059786)
checked immutable proof commit `c701bfeea660473fc31ad9d0c74b76309be3b49f`
on 16 September 2026 UTC. The complete 29-file source graph passed LeanCert
kernel-trust assertions, actual non-root sandboxed Comparator, default-kernel
replay, standard transitive axiom checks and all required per-project controls.
The [authenticated evidence](verification/linux-2026-09-16) binds all 634 candidate
inputs. Two [independent final mathematical/runtime referees](reviews/final)
accepted the full source and observed execution. All original mathematical,
frozen boundary, configuration and historical evidence bytes remain unchanged.
Later publication and merge commits require their own exact-commit checks.


Start with [the numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/MF22/Definitions.lean) and [Challenge](Challenge.lean). The final implication is [polynomial_conditioning](NLA/MF22/Conditioning.lean); [Solution](Solution.lean) imports the complete graph and checks all 22 exports. [Current source correspondence](SourceCorrespondence-current.md), [proof architecture](PROOF-ARCHITECTURE.md), [export locations](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml) and [canonical evidence inventory](PUBLICATION-ACCEPTANCE.json) provide the audit trail.

The proof derives the exact four-state recurrence, classifies its roots, proves noncancellation and the actual finite inverse, and cancels the growing Green terms before bounding entries. Uniform inverse-entry bounds and dimension-times-entry estimates for both operator norms give the sufficient exponent 2. Fixed-size algebra and an exact completed square remove parameter interval searches. LeanCert certifies the remaining positive integer margin in kernel mode; every exported declaration has a kernel-trust assertion. No native-evaluation or additional-axiom acceptance occurred in the actual canonical run.

With the pinned toolchain and dependencies available, `lake build` now selects the complete Solution graph. The original statement-phase default is retained in the packaging record; changing this default changes no mathematical source or dependency pin. For authoritative verification from a fresh committed repository, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-22/lean /absolute/path/to/nla-lean-tools
```

These commands require the supported non-root Linux isolation environment. The shared verifier runs fresh problem-specific controls, Comparator and default-kernel replay; a development build or source review does not substitute for them. [comparator.json](comparator.json) lists all 22 targets, has no definition holes and allows only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The actual canonical run reported exactly these three axioms for each of the 22 exports. The separate workflow checker-controls job was skipped for the unchanged harness; all required controls actually ran inside the successful project verify job.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI assistance. Bogoya, Böttcher, Ferrari, Grudsky and Serra-Capizzano retain credit for the family, question and source root classification; George Stepaniants is separately credited for the retained manuscript. The [review protocol](../../../docs/lean/REVIEW.md) adapts Tau Ceti standards and does not claim Tau Ceti or human endorsement. Schiffer and Forsythe informed the organization; Mathlib, LeanCert and Lean Comparator supply the pinned foundations and checking tools. License: [Apache 2.0](LICENSE).

The frozen [original correspondence](SourceCorrespondence.md) and
[numerical targets](NUMERICAL_TARGETS.md) retain their historical statement-phase
wording as immutable evidence. Current acceptance is documented above and in
[SourceCorrespondence-current.md](SourceCorrespondence-current.md); the old
proof-free wording does not describe this complete accepted implementation.
Original development builds, failures, source reviews and proof-only repairs
remain unchanged in the retained evidence. This is one accepted proof execution
audited by independent agents, not two independently rerun Lean executions.
