import NLA.KE05.FirstOrdering

/- Exact 2×2 cancellation in George Stepaniants's KE-05 construction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.KE05

lemma det_similarity {b : ℕ} (O D : Mat b) (hO : O.det ≠ 0) :
    (O⁻¹ * D * O).det = D.det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have hi := O.det_nonsing_inv_mul_det hO.isUnit
  calc
    _ = D.det * ((O⁻¹).det * O.det) := by ring
    _ = D.det := by rw [hi, mul_one]

lemma trace_similarity {b : ℕ} (O D : Mat b) (hO : O.det ≠ 0) :
    (O⁻¹ * D * O).trace = D.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv O hO.isUnit, Matrix.one_mul]

lemma X_det (w : Sample 2 3) (hw : (omega w 1).det ≠ 0) : (X w).det = 2 := by
  rw [X, det_similarity _ _ hw]
  norm_num [Matrix.det_fin_two, Matrix.diagonal]

lemma P_det (w : Sample 2 3) (hw : (omega w 2).det ≠ 0) : (P w).det = 0 := by
  rw [P, det_similarity _ _ hw]
  norm_num [Matrix.det_fin_two, Matrix.diagonal]

lemma P_trace (w : Sample 2 3) (hw : (omega w 2).det ≠ 0) : (P w).trace = 1 := by
  rw [P, trace_similarity _ _ hw]
  norm_num [Matrix.trace, Fin.sum_univ_two, Matrix.diagonal]

lemma adjugate_P (w : Sample 2 3) (hw : (omega w 2).det ≠ 0) :
    (P w).adjugate = 1 - P w := by
  have ht := P_trace w hw
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] at ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.sub_apply, Matrix.one_apply] <;> linarith

lemma det_second_difference (e : ℝ) (w : Sample 2 3)
    (h1 : (omega w 1).det ≠ 0) (h2 : (omega w 2).det ≠ 0) :
    (e • X w - P w).det = e * (2*e-kappa w) := by
  have hid : (e • X w-P w).det = e^2*(X w).det+(P w).det -
      e*((P w).adjugate*X w).trace := by
    simp [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul, dotProduct]
    ring
  rw [hid, X_det w h1, P_det w h2, adjugate_P w h2]
  unfold kappa
  ring

lemma adjugate_second_difference (e : ℝ) (w : Sample 2 3)
    (h2 : (omega w 2).det ≠ 0) :
    (e • X w - P w).adjugate = e • (X w).adjugate - (1-P w) := by
  rw [← adjugate_P w h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.sub_apply, Matrix.smul_apply] <;> ring

lemma inverse_product {b : ℕ} (A B : Mat b) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A*B)⁻¹ = B⁻¹*A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul A hA.isUnit,
    Matrix.one_mul, Matrix.nonsing_inv_mul B hB.isUnit]

lemma first_hat_one_similarity (e : ℝ) (w : Sample 2 3) (hw : Valid (witnessData e) w) :
    (recurrence (witnessData e) w 0).hat 1 =
      (e • X w-P w)⁻¹ * (e • X w) * (e • X w-P w) := by
  have hs : (e • X w-P w).det ≠ 0 := by
    have h := hw.2 0 1
    rw [first_lastS_one, Matrix.det_mul] at h
    exact (mul_ne_zero_iff.mp h).2
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 1).2.2, first_lastS_one, rootOrder_zero,
    inverse_product _ _ (hw.1 1) hs]
  change ((e • X w-P w)⁻¹*(omega w 1)⁻¹)*
    Matrix.diagonal (![e,2*e] : Fin 2 → ℝ)*(omega w 1*(e • X w-P w)) = _
  have h := base_witness_one e w
  change (omega w 1)⁻¹*Matrix.diagonal (![e,2*e] : Fin 2 → ℝ)*omega w 1 = _ at h
  simpa only [Matrix.mul_assoc] using congrArg (fun A => (e • X w-P w)⁻¹*A*(e • X w-P w)) h

lemma first_hat_one_cancelled (e : ℝ) (he : e ≠ 0) (w : Sample 2 3)
    (hw : Valid (witnessData e) w) :
    (recurrence (witnessData e) w 0).hat 1 =
      (2*e-kappa w)⁻¹ • ((e • (X w).adjugate-(1-P w))*X w*(e • X w-P w)) := by
  have hs : (e • X w-P w).det ≠ 0 := by
    have h := hw.2 0 1
    rw [first_lastS_one, Matrix.det_mul] at h
    exact (mul_ne_zero_iff.mp h).2
  have hk : 2*e-kappa w ≠ 0 := by
    rw [det_second_difference e w (hw.1 1) (hw.1 2)] at hs
    exact (mul_ne_zero_iff.mp hs).2
  rw [first_hat_one_similarity e w hw, Matrix.inv_def, Ring.inverse_eq_inv,
    det_second_difference e w (hw.1 1) (hw.1 2),
    adjugate_second_difference e w (hw.1 2)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

end NLA.KE05
