# SP-15 LU optimization before code

The frozen target is unchanged: all 81 entries of the actual real matrix equation `jacobianMinor = lowerCertificate * upperCertificate`, all triangular/diagonal claims and the exact determinant -1088. No table, definition or header changes are permitted.

Actual local79 passed BoxGeometry but the monolithic JacobianCertificate process exceeded the existing 180-second module limit and was stopped with an empty diagnostic log. No row or Jacobian theorem acceptance may be inferred from that run. Its complete receipt/log and exact failed source are retained here. Default 200,000 heartbeats, one compiler/thread, 4096MiB and the module time limit remain unchanged.

Root explicitly approved this optimization in the task message before implementation: derive typed scalar goals from the frozen literal tables, let Lean's `change` check every lookup, and first time a small batch before generating/running all rows.

Each new immutable row module states the actual equality for that row and every `j : Fin 9`. The proof rewrites only `Matrix.mul_apply`, `Fin.sum_univ_succ` and `Fin.sum_univ_zero`, then handles the nine column cases. Each case uses `change` to expose the exact real scalar target and exactly nine literal products in the same right-associated order as the finite sum, including all zero factors. Lean's definitional equality check must tie those literals to the original frozen matrices and actual indices. `norm_num` then simplifies zero products before rational arithmetic. There is no substituted answer, numerical oracle, native evaluation, weakened equality, or determinant permutation enumeration.

A source-only generator may read the frozen literal tables and emit these goals. It must record its source/input hashes and all emitted row/column coverage; generated text is not itself evidence of correctness. Actual Lean checks every `change` and arithmetic proof. The table bridge remains mandatory, so an accidental generator mismatch is rejected rather than assumed.

First batch: row0 (the sparsest) and row8 (the most populated lower-triangular row), each a separate small module with an actual kernel-trust assertion. These 18 scalar entries provide timing evidence across the range; root alone runs them serially. After success at unchanged limits, generate the other seven rows and combine them without recomputing accepted rows. Split the base-value and remaining triangular/product checks into small modules as useful, without claiming they passed in local79.

The final frozen exported headers remain in a thin aggregator; helpers are ordinary proved row equalities with real consumers, not new problem counts or Comparator target replacements. Numerical's kernel LeanCert certificate and the locally passed BoxGeometry remain unchanged. All thirteen frozen files are checked before each handoff.

This plan adds no new mathematical assertion beyond the accepted numerical target. George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, remains credited; prior mathematical and library authorship is preserved, without email. No Lean, Lake, Comparator, Git or network command is invoked by this agent.
