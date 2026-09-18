/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The arbitrary-radius exponential envelope retains the original MF05/Colbrook
attribution. Tensor algebra and norm comparison use the frozen literal tensor.

Both tensor factors come from exactly the same original chronological word.
Continuity, compactness, product algebra and decay are proved for that image.
Fixed dimension constants remain outside the length exponent.
-/
import NLA.MF06.TensorAlgebra
import NLA.MF06.WordImages
import NLA.MF05.GeneralEnvelope

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma continuous_tensorMatrix {m n : ℕ} :
    Continuous (fun p : Square m × Square n => tensorMatrix p.1 p.2) := by
  change Continuous (fun p : Square m × Square n => fun u v =>
    p.1 ((finProdFinEquiv (m := m) (n := n)).symm u).1
        ((finProdFinEquiv (m := m) (n := n)).symm v).1 *
      p.2 ((finProdFinEquiv (m := m) (n := n)).symm u).2
        ((finProdFinEquiv (m := m) (n := n)).symm v).2)
  have hfst : Continuous (fun p : Square m × Square n => p.1) := continuous_fst
  have hsnd : Continuous (fun p : Square m × Square n => p.2) := continuous_snd
  exact continuous_pi fun u => continuous_pi fun v =>
    (hfst.matrix_elem ((finProdFinEquiv (m := m) (n := n)).symm u).1
      ((finProdFinEquiv (m := m) (n := n)).symm v).1).mul
      (hsnd.matrix_elem ((finProdFinEquiv (m := m) (n := n)).symm u).2
        ((finProdFinEquiv (m := m) (n := n)).symm v).2)

lemma pairedFamily_isCompact {d m n : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (f : Square d → Square m) (g : Square d → Square n)
    (hf : Continuous f) (hg : Continuous g) : IsCompact (pairedFamily M f g) :=
  hM.image (continuous_tensorMatrix.comp (hf.prodMk hg))

lemma pairedFamily_nonempty {d m n : ℕ} (M : Set (Square d)) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n) :
    (pairedFamily M f g).Nonempty := hneM.image _

lemma paired_matrixProduct {d m n : ℕ} (f : Square d → Square m)
    (g : Square d → Square n) (w : List (Square d)) :
    matrixProduct (w.map (fun A => tensorMatrix (f A) (g A))) =
      tensorMatrix (matrixProduct (w.map f)) (matrixProduct (w.map g)) := by
  induction w with
  | nil =>
      simp only [List.map_nil, matrixProduct_nil]
      exact (tensor_algebra (1 : Square m) 1 (1 : Square n) 1).1.symm
  | cons A w ih =>
      simp only [List.map_cons, matrixProduct_cons, ih]
      exact (tensor_algebra (matrixProduct (w.map f)) (f A)
        (matrixProduct (w.map g)) (g A)).2.symm

/-- Strictly subunit paired radius controls the product of the two actual
block word norms. The shared original list is never replaced by two choices. -/
lemma paired_word_decay {d m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n)
    (hf : Continuous f) (hg : Continuous g)
    (hradius : jointSpectralRadius (pairedFamily M f g) < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ w : List (Square d), WordIn M w →
        spectralNorm (matrixProduct (w.map f)) * spectralNorm (matrixProduct (w.map g)) ≤
          K * q ^ w.length := by
  have hc := pairedFamily_isCompact M hM f g hf hg
  have hne := pairedFamily_nonempty M hneM f g
  have hdim : 1 ≤ m * n := one_le_mul_of_one_le_of_one_le hm hn
  have hr0 := jointSpectralRadius_nonneg (pairedFamily M f g) hc hne
  obtain ⟨q, hrq, hq1⟩ := exists_between hradius
  have hq : 0 < q := hr0.trans_lt hrq
  obtain ⟨_, K, hK, hbound⟩ := general_exponential_envelope hdim (pairedFamily M f g)
    hc hne q hrq
  have hD : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by exact_mod_cast hdim
  refine ⟨q, hq, hq1, ((m : ℝ) * (n : ℝ)) * K,
    one_le_mul_of_one_le_of_one_le hD hK, ?_⟩
  intro w hw
  calc
    spectralNorm (matrixProduct (w.map f)) * spectralNorm (matrixProduct (w.map g)) ≤
        ((m : ℝ) * (n : ℝ)) *
          spectralNorm (tensorMatrix (matrixProduct (w.map f)) (matrixProduct (w.map g))) :=
      (tensor_norm_comparison hm hn _ _).2
    _ = ((m : ℝ) * (n : ℝ)) *
        spectralNorm (matrixProduct (w.map (fun A => tensorMatrix (f A) (g A)))) := by
      rw [paired_matrixProduct]
    _ ≤ ((m : ℝ) * (n : ℝ)) * familyGrowth (pairedFamily M f g) w.length :=
      mul_le_mul_of_nonneg_left
        (word_le_familyGrowth (pairedFamily M f g) hc w.length
          (w.map (fun A => tensorMatrix (f A) (g A))) (by simp only [List.length_map])
          (word_image_in M (fun A => tensorMatrix (f A) (g A)) w hw))
        (zero_le_one.trans hD)
    _ ≤ ((m : ℝ) * (n : ℝ)) * (K * q ^ w.length) :=
      mul_le_mul_of_nonneg_left (hbound w.length) (zero_le_one.trans hD)
    _ = (((m : ℝ) * (n : ℝ)) * K) * q ^ w.length := (mul_assoc _ _ _).symm

#print axioms paired_word_decay
#assert_trust kernel paired_word_decay

end NLA.MF06
