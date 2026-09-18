/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

A finite diagonal pairing gives independent images in the range of H.
The rank bound counts complete unit-circle multiplicities under the original
simple-root premise, including the empty unit-circle spectrum.
-/
import NLA.MF18.GeneralizedStein
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem unit_nonresonance (lam μ : ℂ) (hlam : ‖lam‖ = 1) (hne : lam ≠ μ) :
    1 - star lam * μ ≠ 0 := by
  have hlam0 : lam ≠ 0 := by
    intro hz
    simpa only [hz, norm_zero, zero_ne_one] using hlam
  have hstar : star lam = lam⁻¹ := (Complex.inv_eq_conj hlam).symm
  intro he
  have hp : star lam * μ = 1 := (sub_eq_zero.mp he).symm
  have hmul := congrArg (fun z : ℂ => lam * z) hp
  have heq : μ = lam := by
    simpa only [hstar, ← mul_assoc, mul_inv_cancel₀ hlam0, one_mul, mul_one] using hmul
  exact hne heq.symm

theorem diagonal_pairing_range_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (H : Mat n) (v : ι → Vec n)
    (hdiag : ∀ i, pairing H (v i) (v i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → pairing H (v i) (v j) = 0) :
    Fintype.card ι ≤ H.rank := by
  classical
  have hlin : LinearIndependent ℂ (fun i => H.mulVec (v i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have he := congrArg (fun y : Vec n => star (v i) ⬝ᵥ y) ha
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      ← pairing_eq_dotProduct] at he
    have hsum : (∑ j : ι, a j * pairing H (v i) (v j)) =
        a i * pairing H (v i) (v i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hoff i j (Ne.symm hji), mul_zero]
      · simp
    rw [hsum] at he
    exact (mul_eq_zero.mp he).resolve_right (hdiag i)
  let w : ι → LinearMap.range H.mulVecLin :=
    fun i => ⟨H.mulVec (v i), ⟨v i, rfl⟩⟩
  have hlinw : LinearIndependent ℂ w :=
    LinearIndependent.of_comp (LinearMap.range H.mulVecLin).subtype hlin
  exact hlinw.fintype_card_le_finrank

theorem stein_rank_lower_bound {n : ℕ} (S H : Mat n)
    (hstein : H = S.conjTranspose * H * S) (hsimple : SimpleCircleRoots S.charpoly)
    (hnonzero : ∀ lam : ℂ, ‖lam‖ = 1 → ∀ v : Vec n, v ≠ 0 →
      S.mulVec v = lam • v → pairing H v v ≠ 0) :
    circleRootCount S.charpoly ≤ H.rank := by
  classical
  let s := (S.charpoly.roots.filter (fun lam : ℂ => ‖lam‖ = 1)).toFinset
  have hmem : ∀ i : s, (i : ℂ) ∈ S.charpoly.roots ∧ ‖(i : ℂ)‖ = 1 := by
    intro i
    exact Multiset.mem_filter.mp (Multiset.mem_toFinset.mp i.property)
  have hev : ∀ i : s, ∃ v : Vec n, v ≠ 0 ∧ S.mulVec v = (i : ℂ) • v := by
    intro i
    have hr : S.toLin'.charpoly.IsRoot (i : ℂ) := by
      simpa only [Matrix.charpoly_toLin'] using Polynomial.isRoot_of_mem_roots (hmem i).1
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly S.toLin' (i : ℂ)).mpr hr).exists_hasEigenvector
    exact ⟨v, hv.2, hv.apply_eq_smul⟩
  choose v hvne hveig using hev
  have hdiag : ∀ i : s, pairing H (v i) (v i) ≠ 0 :=
    fun i => hnonzero i (hmem i).2 (v i) (hvne i) (hveig i)
  have hoff : ∀ i j : s, i ≠ j → pairing H (v i) (v j) = 0 := by
    intro i j hij
    have hneq : (i : ℂ) ≠ (j : ℂ) := fun he => hij (Subtype.ext he)
    apply generalized_stein_pairing S H i j hstein
      (unit_nonresonance i j (hmem i).2 hneq) 1 1
    · simp only [pow_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hveig i, sub_self]
    · simp only [pow_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hveig j, sub_self]
  have hcard : circleRootCount S.charpoly = Fintype.card s := by
    unfold circleRootCount
    rw [← Multiset.toFinset_sum_count_eq]
    calc
      _ = ∑ _i ∈ s, 1 := by
        apply Finset.sum_congr rfl
        intro lam hlam
        have hh := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hlam)
        rw [Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ = 1) (a := lam) hh.2, Polynomial.count_roots,
          hsimple lam hh.2 (Polynomial.isRoot_of_mem_roots hh.1)]
      _ = _ := by simp
  rw [hcard]
  exact diagonal_pairing_range_bound H v hdiag hoff

#print axioms stein_rank_lower_bound

end NLA.MF18
