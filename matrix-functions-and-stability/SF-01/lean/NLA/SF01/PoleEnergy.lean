/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Exact quadratic form of the finite pole matrix. Empty pole families, repeated
poles and zero residue weights are included; no spectral approximation is used.
-/
import NLA.SF01.Definitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma poleMatrix_isHermitian (d : RidgeData) : (poleMatrix d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [poleMatrix]
  · simp [poleMatrix, Matrix.diagonal_apply, hij, Ne.symm hij, mul_comm]

lemma pole_energy (d : RidgeData) (x : Vector (d.size + 1)) :
    x ⬝ᵥ (poleMatrix d *ᵥ x) =
      (∑ j : Fin d.size, d.poles j * x j.succ ^ 2) +
        d.b⁻¹ * (poleVector d ⬝ᵥ x) ^ 2 := by
  have hrow :
      Matrix.of (fun i j => poleVector d i * poleVector d j) *ᵥ x =
        fun i => poleVector d i * (poleVector d ⬝ᵥ x) := by
    funext i
    change (∑ j, (poleVector d i * poleVector d j) * x j) =
      poleVector d i * ∑ j, poleVector d j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have houter : x ⬝ᵥ
      (Matrix.of (fun i j => poleVector d i * poleVector d j) *ᵥ x) =
        (poleVector d ⬝ᵥ x) ^ 2 := by
    rw [hrow]
    simp only [dotProduct]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdiag : x ⬝ᵥ (Matrix.diagonal (poleOffsets d) *ᵥ x) =
      ∑ j : Fin d.size, d.poles j * x j.succ ^ 2 := by
    calc
      x ⬝ᵥ (Matrix.diagonal (poleOffsets d) *ᵥ x) =
          ∑ i : Fin (d.size + 1), poleOffsets d i * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.mulVec_diagonal]
        ring
      _ = ∑ j : Fin d.size, d.poles j * x j.succ ^ 2 := by
        rw [Fin.sum_univ_succ]
        simp [poleOffsets]
  simp only [poleMatrix, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, hdiag, houter, smul_eq_mul]

lemma poleVector_zero_pos (d : RidgeData) (hd : ValidData d) :
    0 < poleVector d 0 := by
  simpa only [poleVector, Fin.cases_zero] using Real.sqrt_pos.mpr hd.1

lemma pole_energy_pos (d : RidgeData) (hd : ValidData d)
    (x : Vector (d.size + 1)) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (poleMatrix d *ᵥ x) := by
  classical
  rw [pole_energy]
  have hs : ∀ j : Fin d.size, 0 ≤ d.poles j * x j.succ ^ 2 :=
    fun j => mul_nonneg (hd.2.2.1 j).le (sq_nonneg _)
  have hb : 0 < d.b⁻¹ := inv_pos.mpr hd.2.1
  by_cases hordinary : ∃ j : Fin d.size, x j.succ ≠ 0
  · obtain ⟨j, hj⟩ := hordinary
    have hsum : 0 < ∑ k : Fin d.size, d.poles k * x k.succ ^ 2 :=
      Finset.sum_pos' (fun k _ => hs k)
        ⟨j, Finset.mem_univ j, mul_pos (hd.2.2.1 j) (sq_pos_of_ne_zero hj)⟩
    exact add_pos_of_pos_of_nonneg hsum (mul_nonneg hb.le (sq_nonneg _))
  · have hzero : ∀ j : Fin d.size, x j.succ = 0 := by
      intro j
      by_contra hj
      exact hordinary ⟨j, hj⟩
    have hxzero : x 0 ≠ 0 := by
      intro hz
      apply hx
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hz
      · exact hzero j
    have hdot : poleVector d ⬝ᵥ x = poleVector d 0 * x 0 := by
      unfold dotProduct
      rw [Fin.sum_univ_succ]
      simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero]
    have hdotnz : poleVector d ⬝ᵥ x ≠ 0 := by
      rw [hdot]
      exact mul_ne_zero (poleVector_zero_pos d hd).ne' hxzero
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun j _ => hs j))
      (mul_pos hb (sq_pos_of_ne_zero hdotnz))

theorem pole_positive_definite (d : RidgeData) (hd : ValidData d) :
    (poleMatrix d).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (poleMatrix_isHermitian d)
  intro x hx
  simpa only [star_trivial] using pole_energy_pos d hd x hx

end
end NLA.SF01
