/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Corollary 7.

The already proved word envelope constructs the particular comparison norm
from its actual supremum. The general comparison bounds all words at once,
including zero radius and infinitely many possible generators.
-/
import NLA.MF05.GeneralComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma comparisonFactor_ge_one (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) :
    1 ≤ comparisonFactor d s :=
  one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr hd) (one_le_pow₀ hs)

lemma comparisonRate_pos {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (L s : ℝ) (hL : 0 < L) (hs : 1 ≤ s) :
    0 < comparisonRate d M L s := by
  have hdpos : (0 : ℝ) < (d : ℝ) := zero_lt_one.trans_le (Nat.one_le_cast.mpr hd)
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hterm : 0 < 2 * (d : ℝ) ^ 2 * L / s := by positivity
  exact add_pos_of_nonneg_of_pos (jointSpectralRadius_nonneg M hM hne) hterm

theorem controlled_comparison_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L s : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hs : 1 ≤ s) :
    0 < comparisonRate d M L s ∧
    IsComplexNorm (comparisonNorm d M L s) ∧
    (∀ x : EuclideanVector d,
      ‖x‖ ≤ comparisonNorm d M L s x ∧
      comparisonNorm d M L s x ≤ comparisonFactor d s * ‖x‖) ∧
    (∀ A ∈ M, ∀ x : EuclideanVector d,
      comparisonNorm d M L s (applyMatrix A x) ≤
        comparisonRate d M L s * comparisonNorm d M L s x) := by
  have hu := comparisonRate_pos hd M hM hne L s hL hs
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map (fun A => A))) ≤
        comparisonFactor d s * (comparisonRate d M L s) ^ w.length := by
    simpa only [List.map_id_fun', id_eq] using
      (word_le_familyGrowth M hM w.length w rfl hw).trans
        (general_quantitative_comparison hd M hM hne L s hL hML hs w.length)
  exact ⟨hu,
    productEnvelope_isComplexNorm M (fun A => A) (comparisonRate d M L s)
      (comparisonFactor d s) hu hword,
    productEnvelope_bounds M (fun A => A) (comparisonRate d M L s)
      (comparisonFactor d s) hu hword,
    productEnvelope_generator M (fun A => A) (comparisonRate d M L s)
      (comparisonFactor d s) hu hword⟩

#print axioms controlled_comparison_norm
#assert_trust kernel controlled_comparison_norm

end NLA.MF05
