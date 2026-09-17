# Essential primary-source reuse

All complete source hashes already bound in 01-PRE-CODE-BINDINGS.json were
rechecked unchanged after implementation. Mathlib remains at the frozen
0df444a360eaa60ab8c11dca51a86af692955474 pin. HANDOFF.json adds the three
small primary-source bindings inspected during authoring.

- PiL2.lean:151 supplies the actual Euclidean squared norm as the finite sum
  of squared coordinate norms. PiLp.lean:1043 supplies the coordinate unit
  vector norm. The endpoint applies the concrete first column to this vector;
  it does not use a degree-restricted coefficient theorem with an unbounded
  symbol.
- Finset/Basic.lean:740 generates add_sum_erase. Order/BigOperators/Group/
  Finset.lean:192 generates sum_eq_zero_iff_of_nonneg. These isolate the known
  unit first term and prove the remaining visible coefficients vanish.
- Operator/Basic.lean:199 opNorm_le_bound and :237 le_opNorm prove both
  compression inequalities directly, with no positive-dimension premise.
- Polynomial/Inductions.lean:40-45 divX and coeff_divX provide the exact
  active-block Toeplitz symbol; the zero constant coefficient handles the
  index immediately above the active block diagonal.
- Fin/Tuple/Basic.lean:117-128 cons coordinates, :526 and :539 snoc coordinates,
  :602 snoc_init_self, and BigOperators/Fin.lean:76,85 generated finite sums
  establish the different first/last embeddings and every-vector decomposition.
- Lp/Matrix.lean:30-52 defines the matrix-to-linear-map equivalence and identity
  action; PiL2.lean:1243 defines toEuclideanLin as toLpLin 2 2. The commented
  changes expose these same coordinate maps, preserving the Euclidean space.
- Polynomial/Degree/Defs.lean:141-162 supplies the degree/natDegree conversion
  and constant/unit degree. Coprime/Basic.lean:97 supplies isCoprime_one_right.
  Dimension/Finrank.lean:139 and PiL2.lean:207 supply the top-submodule and
  Euclidean dimension equalities.
- Order/GroupWithZero/Basic.lean:705,715 supplies nonnegative square equality
  and comparison. GroupWithZero/Basic.lean:262 supplies sq_eq_zero_iff.
- Project reuse is genuine: coefficient_roundtrip constructs the entire
  endpoint maximal subspace; maximal_space_norm identifies it with top;
  toeplitz_one/toeplitz_C/toeplitz_action/coeffVector_mul_truncate supply its
  interpolation and polynomial action clauses. SchurBasicNorms was read as
  a previously checked matrix-wrapper example, and is not an import.

The three explicitly added Mathlib imports have sources and cached olean files
present, checked read-only. Presence is not a claim that either new source has
elaborated or that a cached dependency has been accepted for a new runner run.
The author ran no Lean, Lake, cache, Git or network command.
