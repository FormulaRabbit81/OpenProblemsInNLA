import NLA.KE05.LimitAlgebra
import NLA.KE05.GenericWitness
import NLA.KE05.GenericValidity
import NLA.KE05.ProbabilityBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace NLA.KE05

lemma epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0) := by
  have h : Tendsto (fun m : ℕ => (m : ℝ)+6) atTop atTop :=
    tendsto_atTop_mono (fun m => le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  unfold epsilon
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp h

lemma continuous_spectralNorm {b : ℕ} : Continuous (spectralNorm (b := b)) := by
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin b)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional).norm

lemma spectralNorm_pos_of_ne_zero {b : ℕ} (A : Mat b) (hA : A ≠ 0) :
    0 < spectralNorm A := by
  apply norm_pos_iff.mpr
  intro h
  apply hA
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin b)).injective (by simpa using h)

lemma limitMatrix_pos (w : Sample 2 3) (hk : kappa w ≠ 0) (hq : Q w 0 0 ≠ 0) :
    0 < spectralNorm (limitMatrix w) := by
  apply spectralNorm_pos_of_ne_zero
  intro h
  have hh := congrArg (fun A : Mat 2 => A 0 0) h
  change (-1/kappa w)*(Q w 0 0) = 0 at hh
  exact mul_ne_zero (div_ne_zero (by norm_num) hk) hq hh

lemma first_hat_limit (w : Sample 2 3) (hk : kappa w ≠ 0)
    (hw : ∀ m : ℕ, Valid (witnessData (epsilon m)) w) :
    Tendsto (fun m : ℕ => (recurrence (witnessData (epsilon m)) w 0).hat 1)
      atTop (nhds (limitMatrix w)) := by
  have hden : Tendsto (fun m => 2*epsilon m-kappa w) atTop (nhds (-kappa w)) := by
    simpa using (tendsto_const_nhds.mul epsilon_tendsto_zero).sub tendsto_const_nhds
  have hnum : Tendsto (fun m => (epsilon m • (X w).adjugate-(1-P w))*X w*(epsilon m • X w-P w))
      atTop (nhds (Q w)) := by
    have hleft : Tendsto (fun m => epsilon m • (X w).adjugate-(1-P w))
        atTop (nhds (-(1-P w))) := by
      simpa using (epsilon_tendsto_zero.smul
        (tendsto_const_nhds (x := (X w).adjugate))).sub (tendsto_const_nhds (x := 1-P w))
    have hright : Tendsto (fun m => epsilon m • X w-P w) atTop (nhds (-P w)) := by
      simpa using (epsilon_tendsto_zero.smul
        (tendsto_const_nhds (x := X w))).sub (tendsto_const_nhds (x := P w))
    simpa only [Q, neg_mul, mul_neg, neg_neg] using (hleft.mul (tendsto_const_nhds (x := X w))).mul hright

  have h := (hden.inv₀ (neg_ne_zero.mpr hk)).smul hnum
  have heq : ∀ m, (recurrence (witnessData (epsilon m)) w 0).hat 1 =
      (2*epsilon m-kappa w)⁻¹ •
        ((epsilon m • (X w).adjugate-(1-P w))*X w*(epsilon m • X w-P w)) :=
    fun m => first_hat_one_cancelled _ (epsilon_range m).1.ne' w (hw m)
  simpa only [← heq, limitMatrix, inv_neg, neg_div, one_div] using h

 theorem probability_one_nonzero_limit_proved :
    ∀ᵐ w ∂gaussianLaw 2 3,
      kappa w ≠ 0 ∧ Q w 0 0 ≠ 0 ∧
      (∀ m : ℕ, Valid (witnessData (epsilon m)) w) ∧
      Tendsto (fun m : ℕ => (recurrence (witnessData (epsilon m)) w 0).hat 1)
        atTop (nhds (limitMatrix w)) ∧ 0 < spectralNorm (limitMatrix w) := by
  have hv : ∀ᵐ w ∂gaussianLaw 2 3, ∀ m : ℕ, Valid (witnessData (epsilon m)) w :=
    ae_all_iff.mpr (fun m => all_orderings_valid_ae _ (witness_admissible _ (epsilon_range m)))
  filter_upwards [nonzero_limit_numerators_ae, hv] with w hn hw
  exact ⟨hn.1, hn.2, hw, first_hat_limit w hn.1 hw, limitMatrix_pos w hn.1 hn.2⟩

end NLA.KE05
