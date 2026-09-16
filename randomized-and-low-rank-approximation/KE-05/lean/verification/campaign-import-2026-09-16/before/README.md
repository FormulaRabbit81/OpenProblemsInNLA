# KE-05 Lean formalization

This project proves the complete negative answer to KE-05. It retains the prescribed descending matrix recurrence, all root orderings, actual Euclidean operator norms, independent standard-real Gaussian entries, and every dimension and confidence quantifier in the conjecture. The deterministic b=2,d=3 spectral family suffices to refute the full universal claim.

The mathematical proof is by George Stepaniants; the original interpolation framework and conjecture are by Nian Shao. Formalization: Sidney Holden with OpenAI Codex assistance. No source-author endorsement or external human peer review is asserted.

Two independent nonauthor statement reviews preceded implementation. [The freeze](verification/statement-freeze.json) and [numerical plan](NUMERICAL_TARGETS.md) retain the exact mathematical boundary. Challenge has ten deliberate placeholders and is never imported by Solution. The only build-configuration addition registers the Solution library; [the revision record](verification/build-config-revision.json) retains the prior bytes and unchanged pins.

[Proof notes](PROOF_NOTES.md) describe the literal-recurrence bridge, Gaussian polynomial null-set argument, exact two-by-two cancellation, genuine norm lower bound and marginal-probability limit. There is no finite-sample or scalar-only substitute for the random matrix theorem.

All ten [Solution](Solution.lean) exports pass local Lean elaboration and LeanCert kernel trust checks with only `propext`, `Classical.choice`, and `Quot.sound`. The normal build and [local proof receipt](verification/local-proof.json) retain exact evidence. Both independent final reviews and [fresh isolated Linux Comparator/default-kernel verification](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34927150695) passed at `9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6`. Actual sandbox and rejection controls passed. [Retained evidence](../../../docs/lean/verification-2026-09-15/KE-05/README.md) binds the tested inputs to that immutable revision.

[Comparator](comparator.json) selects all ten statements with no definition exceptions. [formalization.yaml](formalization.yaml) records scope, authorship and automation. Agent reviews apply the repository's Tau Ceti adaptation; they are not official Tau Ceti endorsement.
