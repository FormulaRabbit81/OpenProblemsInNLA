import NLA.KE05.Recurrence
import NLA.KE05.Endpoints

/- Exact first-root recurrence identities from George Stepaniants's proof.
The determinant bound uses actual similarities and the prescribed pivots. -/
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma scalar_similarity {b : ℕ} (O : Mat b) (hO : O.det ≠ 0) (c : ℝ) :
    O⁻¹ * (c • (1 : Mat b)) * O = c • (1 : Mat b) := by
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [Matrix.nonsing_inv_mul O hO.isUnit]

lemma det_scalar_sub_similarity {b : ℕ} (O D : Mat b) (hO : O.det ≠ 0) (c : ℝ) :
    (c • (1 : Mat b) - O⁻¹ * D * O).det = (c • (1 : Mat b) - D).det := by
  have he : c • (1 : Mat b) - O⁻¹ * D * O = O⁻¹ * (c • (1 : Mat b) - D) * O := by
    rw [Matrix.mul_sub, Matrix.sub_mul, scalar_similarity O hO c]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  have hi := O.det_nonsing_inv_mul_det hO.isUnit
  calc
    _ = (c • (1 : Mat b) - D).det * ((O⁻¹).det * O.det) := by ring
    _ = (c • (1 : Mat b) - D).det := by rw [hi, mul_one]

lemma base_witness_two (e : ℝ) (w : Sample 2 3) : baseBlock (witnessData e) w 0 2 = P w := rfl

lemma base_witness_one (e : ℝ) (w : Sample 2 3) : baseBlock (witnessData e) w 0 1 = e • X w := by
  have hd : Matrix.diagonal (![e,2*e] : Fin 2 → ℝ) = e • Matrix.diagonal (![1,2] : Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mul_comm]
  change (omega w 1)⁻¹ * Matrix.diagonal (![e,2*e] : Fin 2 → ℝ) * omega w 1 = _
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]
  rfl

lemma base_witness_zero (e : ℝ) (w : Sample 2 3) (hw : (omega w 0).det ≠ 0) :
    baseBlock (witnessData e) w 0 0 = (2 : ℝ) • (1 : Mat 2) := by
  have hd : Matrix.diagonal (![2,2] : Fin 2 → ℝ) = (2 : ℝ) • (1 : Mat 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Matrix.one_apply]
  change (omega w 0)⁻¹ * Matrix.diagonal (![2,2] : Fin 2 → ℝ) * omega w 0 = _
  rw [hd]
  exact scalar_similarity _ hw 2

lemma first_lastS_two (e : ℝ) (w : Sample 2 3) : (recurrence (witnessData e) w 0).lastS 2 = 1 := by
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 2).2.1]
  rfl

lemma first_hat_two (e : ℝ) (w : Sample 2 3) : (recurrence (witnessData e) w 0).hat 2 = P w := by
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 2).2.2, first_lastS_two]
  simp only [Matrix.mul_one]
  rfl

lemma first_lastS_one (e : ℝ) (w : Sample 2 3) :
    (recurrence (witnessData e) w 0).lastS 1 = e • X w - P w := by
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 1).2.1]
  change baseBlock (witnessData e) w 0 1 * 1 - 1 * (recurrence (witnessData e) w 0).hat 2 = _
  rw [Matrix.mul_one, Matrix.one_mul, base_witness_one, first_hat_two]

lemma first_lastS_zero (e : ℝ) (w : Sample 2 3) (hw : (omega w 0).det ≠ 0) :
    (recurrence (witnessData e) w 0).lastS 0 =
      ((2 : ℝ) • (1 : Mat 2) - (recurrence (witnessData e) w 0).hat 1) *
      ((2 : ℝ) • (1 : Mat 2) - P w) := by
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 0).2.1]
  change baseBlock (witnessData e) w 0 0 *
      (baseBlock (witnessData e) w 0 0 * 1 - 1 * (recurrence (witnessData e) w 0).hat 1) -
    (baseBlock (witnessData e) w 0 0 * 1 - 1 * (recurrence (witnessData e) w 0).hat 1) *
      (recurrence (witnessData e) w 0).hat 2 = _
  rw [base_witness_zero e w hw, first_hat_two]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]

lemma first_lastS_determinant (e : ℝ) (w : Sample 2 3) (hw : Valid (witnessData e) w) :
    ((recurrence (witnessData e) w 0).lastS 0).det = 2*(2-e)*(2-2*e) := by
  rw [first_lastS_zero e w (hw.1 0), Matrix.det_mul]
  rw [(literal_recurrence_contract_proved (witnessData e) w 0 1).2.2]
  rw [det_scalar_sub_similarity _ _ (hw.2 0 1) 2]
  change (2 • (1 : Mat 2) - Matrix.diagonal (![e,2*e] : Fin 2 → ℝ)).det *
      (2 • (1 : Mat 2) - (omega w 2)⁻¹ * Matrix.diagonal (![0,1] : Fin 2 → ℝ) * omega w 2).det = _
  rw [det_scalar_sub_similarity _ _ (hw.1 2) 2]
  norm_num [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal]
  ring

end NLA.KE05
