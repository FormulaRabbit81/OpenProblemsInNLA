# NM-04 canonical Linux verification, 17 September 2026

Actual [run 35276203784](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35276203784/job/105387449317) checked literal proof commit `21ed3545a8b4784303e9cc0473879eb33ef4d813`. The retained GitHub metadata, artifact ZIP and raw logs authenticate all 380 tracked project inputs and all 35 exports. Comparator statement matching, Lean's default kernel, permitted transitive axioms and the actual per-project sandbox and rejection controls passed.

ROOT-AUDIT.json records the coordinator's inspection of the actual execution and source identity. That inspection is not another compiler run. Source-bound local macOS compilation is recorded separately in ../LOCAL-COMPLETE.json. The global checker-controls job was skipped because shared tooling was unchanged; the required controls executed within NM-04's successful verification job.

Only Challenge's 35 deliberate specification placeholders used `sorry`. Solution never imports Challenge and contains no proof holes. Every target export has only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Both exact LeanCert half certificates are consumed by coercivity in kernel mode; the remaining argument is symbolic.

This record proves execution at the immutable proof revision. The later documentation/publication commit and upstream PR merge checkout have separate checks, recorded in the PR; no earlier run is claimed to have checked future files.
