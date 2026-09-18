/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Compactness bounds the actual rectangular generator entries. The two diagonal
families are product bounded by hypothesis, while the same-generator paired
radius yields exponential decay of paired word norms. The preceding exact
word estimate then proves genuine product boundedness of the full family.
-/
import NLA.MF06.TwoBlockEstimates

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma continuous_twoBlock_family {d m n : ℕ} (f : Square d → Square m)
    (g : Square d → Square n) (h : Square d → Matrix (Fin m) (Fin n) ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun A => twoBlockMatrix (f A) (h A) (g A)) := by
  exact (hf.matrix_fromBlocks hh continuous_const hg).matrix_submatrix _ _

/-- A finite entry sum supplies a compactness bound without introducing a
rectangular operator-norm convention. No nonempty index type is needed. -/
lemma compact_rectangular_entry_bound {d m n : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (h : Square d → Matrix (Fin m) (Fin n) ℂ) (hh : Continuous h) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ A ∈ M, ∀ i j, ‖h A i j‖ ≤ L := by
  let total : Square d → ℝ := fun A => ∑ i : Fin m, ∑ j : Fin n, ‖h A i j‖
  have htotal : Continuous total :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hh.matrix_elem i j).norm
  obtain ⟨L, hL⟩ := hM.bddAbove_image htotal.continuousOn
  refine ⟨max 0 L, le_max_left _ _, ?_⟩
  intro A hA i j
  have hrow : ‖h A i j‖ ≤ ∑ v : Fin n, ‖h A i v‖ :=
    Finset.single_le_sum (fun v _ => norm_nonneg (h A i v)) (Finset.mem_univ j)
  have hsum : (∑ v : Fin n, ‖h A i v‖) ≤ total A :=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun v _ => norm_nonneg (h A u v))
      (Finset.mem_univ i)
  exact (hrow.trans hsum).trans ((hL ⟨A, hA, rfl⟩).trans (le_max_right _ _))

/-- The complete two-block nonresonance implication for arbitrary compact
families and continuous maps of the same original generator. -/
lemma twoBlock_product_bounded {d m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n)
    (h : Square d → Matrix (Fin m) (Fin n) ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfb : IsProductBounded (f '' M)) (hgb : IsProductBounded (g '' M))
    (hpair : jointSpectralRadius (pairedFamily M f g) < 1) :
    IsProductBounded ((fun A => twoBlockMatrix (f A) (h A) (g A)) '' M) := by
  obtain ⟨Kf, hKf, hfb⟩ := hfb
  obtain ⟨Kg, hKg, hgb⟩ := hgb
  let K : ℝ := max Kf Kg
  have hK : 0 ≤ K := (zero_le_one.trans hKf).trans (le_max_left _ _)
  have hfw (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map f)) ≤ K :=
    ((word_le_familyGrowth (f '' M) (hM.image hf) w.length (w.map f)
      (by simp only [List.length_map]) (word_image_in M f w hw)).trans (hfb w.length)).trans
        (le_max_left _ _)
  have hgw (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map g)) ≤ K :=
    ((word_le_familyGrowth (g '' M) (hM.image hg) w.length (w.map g)
      (by simp only [List.length_map]) (word_image_in M g w hw)).trans (hgb w.length)).trans
        (le_max_right _ _)
  obtain ⟨q, hq, hq1, F, hF, hdecay⟩ := paired_word_decay hm hn M hM hneM f g hf hg hpair
  obtain ⟨L, hL, hentries⟩ := compact_rectangular_entry_bound M hM h hh
  let H : Square d → Square (m + n) := fun A => twoBlockMatrix (f A) (h A) (g A)
  have hH : Continuous H := continuous_twoBlock_family f g h hf hg hh
  let C : ℝ := ((m + n : ℕ) : ℝ) * (K + ((m : ℝ) * (n : ℝ) * L) *
    (2 * K ^ 2 + 4 * (((K ^ 4 * F / q) * q) / (1 - q) ^ 2) + 1))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro k
  obtain ⟨w, _, hw, he⟩ := familyGrowth_attained (H '' M) (hM.image hH) (hneM.image H) k
  obtain ⟨v, hv, rfl⟩ := word_image_preimage M H w hw
  rw [← he]
  exact (twoBlock_word_bound M f g h K F q L hK (zero_le_one.trans hF) hq hq1 hL
    hfw hgw hdecay hentries v hv).trans (le_max_right 1 C)

#print axioms twoBlock_product_bounded
#assert_trust kernel twoBlock_product_bounded

end NLA.MF06
