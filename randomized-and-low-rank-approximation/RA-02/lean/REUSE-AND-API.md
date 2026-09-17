# RA-02 reuse and pinned API notes

Source inspection only; no Lean, Lake, cache, proof implementation or runtime
acceptance is claimed. PRIMARY-API.json binds 13 complete primary source files
by their Git blob IDs and SHA-256 hashes to the retained complete tree for
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The statement author read the
matrix spectral and positivity interfaces, and the independent semantic
investigator supplied separately retained notes with exact inspected ranges.
Full byte authentication is not a claim that every line of every imported
library proof was reviewed here.

The trusted base uses Mathlib's `Matrix.PosSemidef` and `Matrix.PosDef`, complex
matrices, actual conjugate quadratic form, `Complex.normSq`, and actual
`Matrix.IsHermitian.eigenvalues₀`. In particular, eigenvalues₀ is antitone;
`eigenvalues` uses a separate cardinality reindexing and is not silently used
as a sorted list. The definition explicitly casts a Fin n index to
Fin(card(Fin n)). These library notions are not replaced by problem-specific
structures carrying unproved positivity or spectral conclusions.

The matrix spectrum file supplies sortedness, actual eigenvectors, spectral
membership and trace sum. Existing `Matrix.PosDef.eigenvalues_pos` and
`PosSemidef.eigenvalues_nonneg` supply genuine spectral positivity after the
explicit reindexing. The least-eigenvalue Rayleigh obligation can use the
symmetric-map Rayleigh-infimum eigenvalue theorem and sortedness, with the
existing norm bound for a general Hermitian map. This keeps chosen eigenvalue
and eigenbasis implementations opaque. PSD inputs have the simpler lower
bound zero. The singleton rank-r tail at order r+1 is a finite-index identity,
not a numerical estimate.

Generic PSD updates can use `PosSemidef.conjTranspose_mul_mul_same` and the
exact congruence with I-e_j row_j(R)/R_jj. Diagonal/trace nonnegativity,
Hermitian scalar reality and `PosSemidef.trace_eq_zero_iff` support the real
conditional law. The fixed 2-by-2 compression/determinant argument in the
retained API notes proves that zero diagonal implies zero row/column when
needed; it is an all-dimension symbolic lemma, not numerical enumeration.
The totalized zero-diagonal update and uniform zero-residual kernel avoid
undefined branches while preserving the original distribution of residuals.

A proved nonnegative normalized finite path-weight sum is the selected
probability representation. Standard PMF packaging is available, but introduces
unnecessary ENNReal conversion for a finite expectation. Normalization, PSD,
zero events, zero absorption and conditional recursion are explicit frozen
obligations, so this choice does not omit probability semantics. No stochastic
independence is assumed. List.ofFn is only the chronology-preserving bridge
from finite function histories to recursively defined path weights.

`Real.one_add_inv_pow_le_exp` supplies the symbolic rank-dependent bound.
`Real.tendsto_exp_mul_div_rpow_atTop` supplies exponential domination for
arbitrary real exponents. The sole numerical LeanCert certificate is planned
at exp(1)<=3, using explicit kernel trust. Its source syntax was inspected in
MF-07's Numerical module, but no future MF-07 proof is imported, copied into
the active draft, or assumed. No other project's runtime acceptance is counted
for RA-02. Exact real powers and finite products remain symbolic.

The entire retained Schiffer Challenge and Forsythe Challenge/numerical-first
document were read as organization examples. Their exact snapshot bindings
are in REUSE-AUDIT.json. No theorem or bespoke definition from either project
is imported. The future independent Challenge/Solution separation follows
that pattern, with all 27 contracts and no definition holes.

Tau Ceti correctness, generality, proof-quality, attribution and reuse criteria
are scoped in REVIEW-PLAN.md. Full Mathlib-wide semantic theorem search was
not performed at this statement-only stage; located primary APIs above will
be reused rather than rederived during the authorized implementation. The
fresh public audit is likewise explicitly bounded, not an assertion that
private or unusually named work does not exist.
