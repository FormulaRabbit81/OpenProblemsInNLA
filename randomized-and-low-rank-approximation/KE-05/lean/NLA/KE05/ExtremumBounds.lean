import NLA.KE05.MatrixBounds
import NLA.KE05.Endpoints

/- Bounds are taken against the genuine finite sSup expressions in Definitions. -/
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma spectralNorm_neg {b : ℕ} (A : Mat b) : spectralNorm (-A) = spectralNorm A := by
  simp [spectralNorm]

lemma spectralNorm_diagonal {b : ℕ} (v : Fin b → ℝ) :
    spectralNorm (Matrix.diagonal v) = ‖v‖ := by
  rw [spectralNorm, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

lemma witness_second_norm (e : ℝ) (he : 0 < e) :
    spectralNorm (Matrix.diagonal (![e,2*e] : Fin 2 → ℝ)) = 2*e := by
  rw [spectralNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, abs_of_pos he, abs_of_pos (by positivity : 0 < 2*e)] <;> linarith
  · have h := norm_le_pi_norm (![e,2*e] : Fin 2 → ℝ) 1
    simpa [Real.norm_eq_abs, abs_of_pos he] using h

lemma monoOrdering_ratio_le {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i : Fin d) (hi : 1 ≤ i.val) :
    endpointRatio (lowerEndpoint L) ((recurrence L w k).hat i)
      (Matrix.diagonal (L (rootOrder k i))) ≤ monoOrdering L w k := by
  have hb : BddAbove {x | ∃ i : Fin d, 1 ≤ i.val ∧
      (x = endpointRatio (lowerEndpoint L) ((recurrence L w k).hat i)
          (Matrix.diagonal (L (rootOrder k i))) ∨
       x = endpointRatio (upperEndpoint L) ((recurrence L w k).hat i)
          (Matrix.diagonal (L (rootOrder k i))))} := by
    apply Set.Finite.bddAbove
    apply (Set.Finite.union (Set.finite_range (fun i => endpointRatio (lowerEndpoint L)
      ((recurrence L w k).hat i) (Matrix.diagonal (L (rootOrder k i)))))
      (Set.finite_range (fun i => endpointRatio (upperEndpoint L)
      ((recurrence L w k).hat i) (Matrix.diagonal (L (rootOrder k i)))))).subset
    rintro x ⟨i,_,h|h⟩
    · exact Or.inl ⟨i,h.symm⟩
    · exact Or.inr ⟨i,h.symm⟩
  exact (le_csSup hb ⟨i,hi,Or.inl rfl⟩).trans (le_max_right _ _)

lemma monoOrdering_le_mono {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d) :
    monoOrdering L w k ≤ mono L w :=
  le_csSup (Set.finite_range _).bddAbove ⟨k,rfl⟩

lemma coefOrdering_le_coef {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d) :
    coefOrdering L w k ≤ coef L w :=
  le_csSup (Set.finite_range _).bddAbove ⟨k,rfl⟩

lemma witness_mono_lower (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ)/4) (w : Sample 2 3) :
    spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2*e) ≤ mono (witnessData e) w := by
  have h := (monoOrdering_ratio_le (witnessData e) w 0 1 (by decide)).trans
    (monoOrdering_le_mono (witnessData e) w 0)
  rw [witness_lower e he] at h
  have hD : spectralNorm (0 • (1 : Mat 2) - Matrix.diagonal ((witnessData e) (rootOrder 0 1))) = 2*e := by
    simp only [zero_smul, zero_sub, spectralNorm_neg, rootOrder_zero]
    exact witness_second_norm e he.1
  have hDn : spectralNorm (Matrix.diagonal ((witnessData e) (rootOrder 0 1))) = 2*e := by
    simpa only [zero_smul, zero_sub, spectralNorm_neg] using hD
  have hep : 0 < 2*e := mul_pos (by norm_num) he.1
  simpa only [endpointRatio, zero_smul, zero_sub, spectralNorm_neg, hDn,
    hep.ne', and_false, ↓reduceIte] using h

lemma witness_coef_lower (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ)/4) (w : Sample 2 3)
    (hd : 0 < ((recurrence (witnessData e) w 0).lastS 0).det)
    (h8 : ((recurrence (witnessData e) w 0).lastS 0).det ≤ 8) :
    Real.rpow 8 (-(1 : ℝ)/4) ≤ coef (witnessData e) w := by
  have h := inverse_half_norm_lower ((recurrence (witnessData e) w 0).lastS 0) hd h8
  have hc : Real.rpow 8 (-(1 : ℝ)/4) ≤ coefOrdering (witnessData e) w 0 := by
    simpa [coefOrdering, witness_gap e he, firstPosition] using h
  exact hc.trans (coefOrdering_le_coef (witnessData e) w 0)

lemma literal_lower_bound_of_det (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ)/4)
    (w : Sample 2 3) (hw : Valid (witnessData e) w)
    (hd : 0 < ((recurrence (witnessData e) w 0).lastS 0).det)
    (h8 : ((recurrence (witnessData e) w 0).lastS 0).det ≤ 8) :
    Real.rpow 8 (-(1 : ℝ)/4) *
      (spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2*e)) ≤
      totalConstant (witnessData e) w := by
  rw [totalConstant, if_pos hw]
  have hm := witness_mono_lower e he w
  have hc := witness_coef_lower e he w hd h8
  have hn : 0 ≤ spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2*e) :=
    div_nonneg (spectralNorm_nonneg _) (mul_nonneg (by norm_num) he.1.le)
  rw [mul_comm]
  exact mul_le_mul hm hc (Real.rpow_nonneg (by norm_num) _) (hn.trans hm)

end NLA.KE05
