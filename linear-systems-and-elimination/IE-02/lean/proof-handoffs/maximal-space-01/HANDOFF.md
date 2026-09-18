# Maximal-space norm candidate handoff

UNRUN candidate for exactly `NLA.IE02.maximal_space_norm` (contract 7 of 50).
The original header is byte-identical to the frozen Challenge and header
inventory. All 13 frozen inputs were rehashed unchanged before coding and at
seal. No other source module or runner artifact was changed by this task.

The new module uses the frozen Euclidean map and its actual operator norm.
Closedness is direct finite-dimensional library reuse. Forward membership
implies equality of squared norms. Conversely, the zero vector is separate;
a nonzero norm-saturating vector maximizes Gram energy on its sphere, so the
pinned Rayleigh theorem gives its Gram eigen equation. The denominator is
proved nonzero before cancellation. Zero dimension, zero matrix and repeated
maximal singular values are all inside the stated scope.

The numerical/symbolic plan and source bindings were written and hashed while
the candidate was absent. SOURCE.lean.txt is the exact active candidate.
API-EVIDENCE.md identifies the primary pinned APIs. VALIDATION.json records
only actual static checks and explicitly pending checks.

Root must perform the actual local Lean run, inspect the axiom/trust output,
and arrange nonauthor proof review. No compiler, Lake, cache mutation, Git,
network, or Comparator was invoked here. Potential elaboration questions are
limited to representation/instance transport in the documented `change`
steps and Mathlib rewrite inference; no mathematical gap or extra assumption
is known. This is author judgment, not a completed kernel or independent
review result. The rest of IE-02 remains outside this one-contract handoff.
