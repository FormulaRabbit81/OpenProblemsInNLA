/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Definitions
import Mathlib.Tactic

noncomputable section
open Matrix
namespace NLA.PF02

/-- Flattening the actual trace product suffices; no symmetry restriction is needed. -/
lemma trace_factor_rank_le {p q k : ℕ} (M : Mat p q) (A : Fin p → Mat k k)
    (B : Fin q → Mat k k) (h : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ k * k := by
  let U : Matrix (Fin p) (Fin k × Fin k) ℝ := fun i t => A i t.1 t.2
  let V : Matrix (Fin k × Fin k) (Fin q) ℝ := fun t j => B j t.2 t.1
  have heq : M = U * V := by
    ext i j
    rw [← h i j]
    change (∑ a : Fin k, ∑ b : Fin k, A i a b * B j b a) =
      ∑ t : Fin k × Fin k, A i t.1 t.2 * B j t.2 t.1
    simp only [Fintype.sum_prod_type]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

lemma factorization_rank_le {p q k : ℕ} {M : Mat p q} (F : Factorization M k) :
    M.rank ≤ k * k := trace_factor_rank_le M F.val.1 F.val.2 F.property.2.2

/-- Rank six rules out every positive factor size below three, not just the displayed tuples. -/
lemma minimal_three_of_rank_six {M : Mat 6 6} (hrank : M.rank = 6)
    (hthree : Nonempty (Factorization M 3)) : IsPSDRank M 3 := by
  refine ⟨⟨by norm_num, hthree⟩, ?_⟩
  intro k hk
  obtain ⟨hkpos, ⟨F⟩⟩ := hk
  have hbound := factorization_rank_le F
  rw [hrank] at hbound
  by_contra h
  have hklt : k < 3 := Nat.lt_of_not_ge h
  interval_cases k <;> norm_num at *

end NLA.PF02
