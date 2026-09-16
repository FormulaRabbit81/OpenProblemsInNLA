# KE-05 Lean formalization

This project proves the full negative answer to KE-05, retaining the literal matrix recurrence, every root ordering, genuine Euclidean operator norms, independent real standard-Gaussian entries and the original uniform-probability quantifiers. A deterministic family with block size two and three blocks refutes the universal conjecture; no finite-sample or scalar-only claim replaces the matrix theorem.

**Existing formalization: Sidney Holden**, with OpenAI Codex assistance, under [Apache-2.0](LICENSE). **Mathematical proof and this integration/verification submission: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Nian Shao** retains credit for the original framework and conjecture. Integration does not transfer authorship of the existing Lean code. No contact email is published.

The unchanged implementation comes from [Sidney Holden’s immutable source](https://github.com/sidneyholden1/OpenProblemsInNLA/tree/04f3f39beb69d77dbc4a8eadee70259eb89a591a/randomized-and-low-rank-approximation/KE-05/lean). Actual historical [Linux run 34927150695](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34927150695) accepted all ten exports through LeanCert kernel-trust checks, Comparator, Lean default-kernel replay, standard transitive axioms and the required sandbox/rejection controls at proof revision `9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6`. All 23 mathematical files are byte-identical at both revisions. The later historical revision changed only README and formalization metadata inside the project.

**Fresh campaign canonical verification is pending.** Two additional independent nonimplementing AI-agent referees have read the entire proof and original target and separately audited the authenticated historical execution. Their [reviews](reviews/campaign/README.md) and the [import record](verification/campaign-import-2026-09-16/TRANSITION.json) retain exact source/evidence hashes. They inspected a historical execution; this does not claim that a new integration commit has already run. No problem status or campaign count is changed by this candidate.

Read the [numerical targets](NUMERICAL_TARGETS.md), [definitions](NLA/KE05/Definitions.lean), [independent Challenge](Challenge.lean), [proof notes](PROOF_NOTES.md) and all ten [Solution exports](Solution.lean). The historical [statement freeze](verification/statement-freeze.json) remains unchanged. Its earlier Solution-library registration and the current default-target amendment are explicitly recorded; mathematical statements, definitions, dependency pins and Comparator policy are unchanged. Challenge’s ten specification placeholders are never imported by Solution.

Exact two-by-two identities, a proved polynomial null-set theorem for the actual Gaussian law, and measure-theoretic convergence remove interval searches. Ten LeanCert `#assert_trust kernel` checks audit the exported proofs. The permitted axioms are only `propext`, `Classical.choice` and `Quot.sound`; the historical actual run reported these for all ten results.

For a developer build with the pinned dependencies available, run `lake build Solution` from this directory. The documented current default also selects Solution, so plain `lake build` checks the full graph. From the repository root, use the shared [non-root Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/KE-05/lean /absolute/path/to/nla-lean-tools
```

The harness runs actual Comparator, default-kernel replay and problem-specific controls from committed sources. The current campaign uses remote Linux; no local Lean/Lake execution is claimed. [Metadata](formalization.yaml) follows schema v0.4. Reviews follow the repository’s scoped Tau Ceti adaptation, without claiming official endorsement or external human peer review. The Schiffer and Forsythe examples inform the shared organization and checking protocol.
