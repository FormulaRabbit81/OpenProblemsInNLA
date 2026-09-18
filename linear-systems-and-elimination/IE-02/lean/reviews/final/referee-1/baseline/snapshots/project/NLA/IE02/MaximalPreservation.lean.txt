/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

One scalar polynomial factor preserves the entire complex gradient and the
unit norm inside the original maximal Gram kernel. No singular-value
multiplicity restriction or real-polynomial hypothesis is introduced.
-/
import NLA.IE02.ScaledFactorization
import NLA.IE02.WeightedFactorization
import NLA.IE02.WeightedCoefficients
import Mathlib.Tactic.Choose

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem maximal_complex_preservation {n k l : ℕ} (hn : 1 ≤ n)
    (T : Square n) (R : Fin k → Square n) (hT : IsToeplitz T) (hne : T ≠ 0)
    (hR : ∀ j, IsToeplitz (R j)) (f : Fin l → H n) (w : Fin l → ℝ)
    (hf : ∀ j, f j ∈ unitMaximal T) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    ∃ x : H n, x ∈ unitMaximal T ∧
      ∀ i, inner ℂ (euclideanLin T x) (euclideanLin (R i) x) =
        ∑ j, (w j : ℂ) * inner ℂ (euclideanLin T (f j)) (euclideanLin (R i) (f j)) := by
  classical
  obtain ⟨d, a, b, hpair, hparam, haction⟩ := scaled_maximal_factorization hn T hT hne
  let m : ℕ := n - 1 - d
  have hd : d < n := hpair.1
  have hsize : d + m + 1 = n := by omega
  have ha : DegreeLE a d := hpair.2.1.le
  have hb : DegreeLE b d := hpair.2.2.1
  choose q hq hfq using fun j => (hparam (f j)).mp (hf j).1
  choose r hr using hR
  obtain ⟨h, hh, _hcircle, hfactor⟩ := weighted_scalar_factorization m q w hq hw
  have hc := weighted_coefficient_preservation d m a b h q w r ha hb hh hq hfactor
  rw [hsize] at hc
  have hfnorm (j : Fin l) : ‖coeffVector n (b * q j)‖ = 1 := by
    rw [← hfq j]
    exact (hf j).2
  have hnorm : ‖coeffVector n (b * h)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [hfnorm, one_pow, mul_one, hsum] using hc.1
  refine ⟨coeffVector n (b * h), ⟨(hparam _).mpr ⟨h, hh, rfl⟩, hnorm⟩, ?_⟩
  intro i
  calc
    inner ℂ (euclideanLin T (coeffVector n (b * h)))
        (euclideanLin (R i) (coeffVector n (b * h))) =
        (operatorNorm T : ℂ) * inner ℂ (coeffVector n (a * h))
          (euclideanLin (toeplitz n (r i)) (coeffVector n (b * h))) := by
      rw [haction h hh, hr i, inner_smul_left, Complex.conj_ofReal]
    _ = (operatorNorm T : ℂ) * ∑ j, (w j : ℂ) *
        inner ℂ (coeffVector n (a * q j))
          (euclideanLin (toeplitz n (r i)) (coeffVector n (b * q j))) := by
      rw [hc.2 i]
    _ = ∑ j, (w j : ℂ) * ((operatorNorm T : ℂ) *
        inner ℂ (coeffVector n (a * q j))
          (euclideanLin (toeplitz n (r i)) (coeffVector n (b * q j)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ j, (w j : ℂ) * inner ℂ (euclideanLin T (f j))
        (euclideanLin (R i) (f j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hfq j, haction (q j) (hq j), hr i, inner_smul_left, Complex.conj_ofReal]

#print axioms maximal_complex_preservation
#assert_trust kernel maximal_complex_preservation

end
end NLA.IE02
