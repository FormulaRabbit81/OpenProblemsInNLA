# IE-21 Lean proof development

This is an **incomplete formalisation**, with proved supporting results in the
shared `NLA.RowDeletion` library and ordinary, still-unproved main challenge
statements. See [DEVELOPMENT.md](DEVELOPMENT.md) for the proved scope, remaining work, and
reproduction commands, and [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) for the
current numerical specification. The default build imports only proved modules.

## Published scaffold and review boundary

The complete previous scaffold at fork base `775bedc1e33cc0951d08610cc7ba50d2901eda1a` is retained byte for byte
in [verification/published-scaffold](verification/published-scaffold), including
its definitions, challenge, metadata, recorded authorship, review reports and logs.
Those reviews apply to that historical scaffold, not to this development.
The candidate's independent statement/proof review and full isolated Linux
Comparator checking remain outstanding; no canonical problem status is changed.

The current `comparator.json` retains the eventual full target list, including
unproved exports. The draft metadata lists only the implemented results, so the
repository's completed-project verification gates are not expected to pass yet.
IE-22 currently uses the relative in-repository IE-21 dependency; final upstream
packaging still needs an immutable Git/subdirectory pin.
