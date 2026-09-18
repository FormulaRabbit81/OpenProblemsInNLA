# IE-02 actual Linux verification

[Run 35230302016](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35230302016/job/105232489885) checked literal published proof commit `9dc46f23457fed8396ad9f6a77677efe30c87df4`. All 1953 submitted package files and all 50 exported statements are source-bound in the retained API metadata, raw job logs, immutable artifact and result. Default-kernel replay, Comparator, transitive permitted-axiom checks and the actual rejection/isolation controls passed. Both build/export sandbox UIDs were 1001.

[Root audit](ROOT-AUDIT.json), [manual log inspection](ROOT-MANUAL-LOG-REVIEW.json) and the [independent runtime report](../reviews/runtime/REVIEW.md) authenticate the execution evidence. These are audits of a GitHub execution, not extra compiler runs. The preceding local macOS build is separately recorded in [LOCAL-COMPLETE](../LOCAL-COMPLETE.json). The standalone checker-controls matrix job was skipped; all per-proof controls ran inside this successful verify job.

The checker, pins and mathematical sources remain unchanged in the publication documents. Later publication-commit and upstream PR checkouts are separate checks and are not claimed by this earlier run. Executable hashes come from the inspected harness's actual build/revalidation receipt; binary bytes were not separately downloaded and rebuilt by reviewers.
