# MF-05 canonical Linux verification, 17 September 2026

Actual [run 35252365986](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35252365986/job/105307710518) checked literal proof commit `06b8cf49740205c4b7b0b71ee5c636855fbe26a6`. All 193 tracked project inputs and all 14 exports were authenticated against that commit. Comparator, Lean's default kernel, permitted transitive axioms and all per-project rejection and sandbox controls passed. The artifact ZIP, GitHub API metadata, raw job logs and extracted evidence are retained unchanged.

The coordinator audited the actual execution and source identity; see ROOT-AUDIT.json. This audit is not another Lean execution. The preceding source-bound local macOS compilation is recorded separately in ../LOCAL-COMPLETE.json. The global checker-controls job was skipped because shared tooling did not change; the required controls actually ran inside the successful MF-05 verification job.

In the submitted proof sources, only the 14 intentional Challenge specification placeholders use `sorry`. The separate rejection controls deliberately test invalid proofs. Solution has no placeholders, and all advertised results use only `propext`, `Classical.choice` and `Quot.sound`. Published MF07 source files retain their existing style warnings and unchanged authorship; there are no MF05 implementation errors or proof holes.

The later documentation/publication commit preserves every mathematical input, frozen contract and dependency pin. The publication-commit and upstream PR merge-checkout runs remain separate and will be recorded in the PR when completed. This earlier run does not claim to check future documentation.

An [independent nonauthor runtime audit](../../reviews/canonical-runtime.md) also approved the exact existing run after a fresh metadata, artifact and raw-log fetch. The [complete audit packet](../../reviews/canonical-runtime-packet.tar.gz) retains its source bindings and executable read-only verifier. It does not claim another compiler execution.
