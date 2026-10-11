# IE-22 targets

The shared definitions and the complete joint semantic specification are in
[IE-21 NUMERICAL_TARGETS.md](../../IE-21/lean/NUMERICAL_TARGETS.md).
`IE22/Challenge.lean` here independently states all four IE-22 exports.

The default build checks proved transfer implications in `IE22.Transfer`.
Their concentration and uniform-bound hypotheses remain explicit. None of the
four unconditional challenge exports is proved yet; current progress and
reproduction commands are in [DEVELOPMENT.md](../../IE-21/lean/DEVELOPMENT.md).

This development project currently consumes IE-21 through an explicit relative
Lake dependency. It must be replaced by an immutable Git/subDir dependency and
freshly verified before publication. This is not a completed or CI-ready submission.
