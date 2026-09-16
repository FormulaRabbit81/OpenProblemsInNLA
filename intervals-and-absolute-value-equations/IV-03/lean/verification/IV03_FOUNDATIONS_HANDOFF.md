# IV-03 checked proof foundations

The original interval criterion is now locally proved. All four frozen exports
pass LeanCert kernel checks and the normal 8804-job Lake build. The frozen
mathematical boundary is unchanged. Final independent reviews and isolated
Linux Comparator remain pending; see local-proof.json for exact hashes.

## Modules and usable interfaces

- `NLA.IV03.Proof`: 13 kernel-checked lemmas establishing the Z-matrix maximum
  principle, nonsingularity/nonnegative inverse from a positive weight,
  determinant positivity by a homotopy, principal Z-matrix closure, and an
  exact three-by-three negative-minors determinant inequality.
- `NLA.IV03.Principal`: arbitrary embedded principal inverse-M closure and
  positive principal determinants; principal Schur closure for a sum-index
  partition; nonnegative transfer blocks `Q * D⁻¹` and `D⁻¹ * R`; transpose
  closure. Block invertibilities follow from the original inverse-M hypothesis.
- `NLA.IV03.Complementary`: complementary-principal-minor identity from the
  actual block inverse and determinant formulas. Also proves negativity of
  every nonempty inverse principal minor when det A < 0 and all proper
  principal minors of A are positive.
- `NLA.IV03.Adjugate`: full adjugate completion for order n+1 with n ≥ 2.
  `adjugate_completion hn A hp hz` yields det A > 0. Here `hp` gives every
  embedded proper principal determinant positive and `hz` gives off-diagonal
  adjugate entries ≤ 0. The order-zero proper minor is harmless (det = 1).
  `inverseM_of_proper_principal_and_adjugate` additionally takes entrywise A ≥ 0
  and concludes the frozen `IsInverseM A` predicate.

The singular adjugate case uses rank-nullity and a codimension-one nonzero
minor to force adjugate rank ≤ 1. A Z matrix with positive diagonal of order
at least three has rank > 1, established using its 2x2 minors. The negative
case uses the complementary identity and the exact 3x3 contradiction. These
are derived facts, not assumptions supplied to the original target.

## Completion and remaining gates

The cofactor identity, exact Schur comparison and full strong induction are now
implemented in Cofactor, Monotonicity, IntervalStructure, SchurInterval,
IntervalAdjugate and IntervalInduction. Vertices supplies the two base cases.
Solution exposes exactly the four frozen targets. See PROOF_NOTES.md.

Independent final code review and isolated Linux Comparator are still required
before this project is advertised as Lean verified.
