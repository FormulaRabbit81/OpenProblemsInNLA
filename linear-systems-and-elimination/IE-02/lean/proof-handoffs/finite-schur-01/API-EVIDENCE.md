# Finite induction reuse

This source implements accepted plan15 steps1-6 exactly. Pinned
Mathlib/Data/Nat/Init.lean260 supplies Nat.strong_induction_on. The motive
carries the entire matrix, Toeplitz witness and norm-one hypotheses.
Dimension0 contradicts hn; dimension1 uses schur_dimension_one followed by
the full schur_scalar_endpoint. Larger dimensions use schur_diagonal_bound
to choose endpoint equality or strict reduction. schur_active_block supplies
a proved Toeplitz witness for the strictly smaller active matrix; then
schur_pair_step transports the entire11-clause pair back to the given matrix.
No symbol degree restriction, oracle, recursive denominator assumption,
extra certificate or resource change is used. The exact norm-one boundary
and all maximal singular multiplicities remain present.
