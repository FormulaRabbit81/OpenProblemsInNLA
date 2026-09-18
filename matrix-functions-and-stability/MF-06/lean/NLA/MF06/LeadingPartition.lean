/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The last original block is separated from all preceding blocks. Its leading
fiber inherits the original labels with the final label removed. The actual
frozen coordinate enumerations are retained; all dimension and surjectivity
facts are proved rather than added as hypotheses to the final contract.
-/
import NLA.MF06.BlockAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- Label `1` is exactly the last original block; all preceding blocks have label `0`. -/
def lastSplit {d r : ℕ} (b : Fin d → Fin (r + 1)) (j : Fin d) : Fin 2 :=
  if b j = Fin.last r then 1 else 0

lemma lastSplit_eq_zero {d r : ℕ} (b : Fin d → Fin (r + 1)) (j : Fin d) :
    lastSplit b j = 0 ↔ b j ≠ Fin.last r := by
  by_cases h : b j = Fin.last r <;> simp [lastSplit, h]

lemma lastSplit_eq_one {d r : ℕ} (b : Fin d → Fin (r + 1)) (j : Fin d) :
    lastSplit b j = 1 ↔ b j = Fin.last r := by
  by_cases h : b j = Fin.last r <;> simp [lastSplit, h]

lemma lastSplit_surjective {d r : ℕ} (hr : 1 ≤ r) (b : Fin d → Fin (r + 1))
    (hb : Function.Surjective b) : Function.Surjective (lastSplit b) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · obtain ⟨j, hj⟩ := hb (⟨0, hr⟩ : Fin r).castSucc
    refine ⟨j, (lastSplit_eq_zero b j).mpr ?_⟩
    rw [hj]
    exact Fin.castSucc_ne_last _
  · obtain ⟨j, hj⟩ := hb (Fin.last r)
    exact ⟨j, (lastSplit_eq_one b j).mpr hj⟩

lemma lastSplit_upper {d r : ℕ} (b : Fin d → Fin (r + 1)) (A : Square d)
    (hA : IsUpperBlockTriangular b A) : IsUpperBlockTriangular (lastSplit b) A := by
  intro i j hij
  have hi : lastSplit b i = 1 := by omega
  have hj : lastSplit b j = 0 := by omega
  apply hA i j
  rw [(lastSplit_eq_one b i).mp hi]
  exact Fin.lt_last_iff_ne_last.mpr ((lastSplit_eq_zero b j).mp hj)

lemma leading_coordinate_not_last {d r : ℕ} (b : Fin d → Fin (r + 1))
    (u : Fin (blockDim (lastSplit b) 0)) :
    b (blockCoordinate (lastSplit b) 0 u) ≠ Fin.last r :=
  (lastSplit_eq_zero b _).mp (blockCoordinate_label (lastSplit b) 0 u)

lemma final_coordinate_label {d r : ℕ} (b : Fin d → Fin (r + 1))
    (u : Fin (blockDim (lastSplit b) 1)) :
    b (blockCoordinate (lastSplit b) 1 u) = Fin.last r :=
  (lastSplit_eq_one b _).mp (blockCoordinate_label (lastSplit b) 1 u)

/-- The inherited label of a genuine leading coordinate. -/
def leadingBlockLabel {d r : ℕ} (b : Fin d → Fin (r + 1))
    (u : Fin (blockDim (lastSplit b) 0)) : Fin r :=
  (b (blockCoordinate (lastSplit b) 0 u)).castLT
    (Fin.lt_last_iff_ne_last.mpr (leading_coordinate_not_last b u))

lemma leadingBlockLabel_castSucc {d r : ℕ} (b : Fin d → Fin (r + 1))
    (u : Fin (blockDim (lastSplit b) 0)) :
    (leadingBlockLabel b u).castSucc = b (blockCoordinate (lastSplit b) 0 u) := rfl

lemma leadingBlockLabel_surjective {d r : ℕ} (b : Fin d → Fin (r + 1))
    (hb : Function.Surjective b) : Function.Surjective (leadingBlockLabel b) := by
  intro i
  obtain ⟨j, hj⟩ := hb i.castSucc
  have hj0 : lastSplit b j = 0 := (lastSplit_eq_zero b j).mpr (by
    rw [hj]; exact Fin.castSucc_ne_last i)
  obtain ⟨u, hu⟩ := blockCoordinate_covers (lastSplit b) 0 j hj0
  refine ⟨u, Fin.castSucc_inj.mp ?_⟩
  rw [leadingBlockLabel_castSucc, hu, hj]

lemma leadingBlockLabel_upper {d r : ℕ} (b : Fin d → Fin (r + 1)) (A : Square d)
    (hA : IsUpperBlockTriangular b A) :
    IsUpperBlockTriangular (leadingBlockLabel b) (blockMatrix (lastSplit b) 0 A) := by
  intro i j hij
  apply hA (blockCoordinate (lastSplit b) 0 i) (blockCoordinate (lastSplit b) 0 j)
  rw [← leadingBlockLabel_castSucc b j, ← leadingBlockLabel_castSucc b i]
  exact hij

/-- A nested leading fiber belongs to precisely the corresponding original block. -/
lemma leading_nested_coordinate_label {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (u : Fin (blockDim (leadingBlockLabel b) i)) :
    b (blockCoordinate (lastSplit b) 0 (blockCoordinate (leadingBlockLabel b) i u)) =
      i.castSucc := by
  rw [← leadingBlockLabel_castSucc b (blockCoordinate (leadingBlockLabel b) i u),
    blockCoordinate_label (leadingBlockLabel b) i u]

#print axioms leadingBlockLabel_surjective
#assert_trust kernel leadingBlockLabel_surjective
#print axioms leadingBlockLabel_upper
#assert_trust kernel leadingBlockLabel_upper

end NLA.MF06
