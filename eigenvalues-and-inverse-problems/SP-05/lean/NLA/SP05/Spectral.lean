/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Sylvester
import NLA.SP05.Sectors

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder
namespace NLA.SP05

lemma real_spectral_max {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∃ r : ℝ, ∃ v : ι → ℝ, 0 < r ∧ v ≠ 0 ∧ P *ᵥ v = r • v ∧
      (r • (1 : Matrix ι ι ℝ) - P).PosSemidef := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hP.isHermitian.eigenvalues
    Finset.univ_nonempty
  let r := hP.isHermitian.eigenvalues i
  let v : ι → ℝ := hP.isHermitian.eigenvectorBasis i
  have hv : v ≠ 0 := by
    intro hz
    apply hP.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hz j
  refine ⟨r, v, hP.eigenvalues_pos i, hv, hP.isHermitian.mulVec_eigenvectorBasis i, ?_⟩
  have hb : P ≤ algebraMap ℝ (Matrix ι ι ℝ) r := by
    apply (le_algebraMap_iff_spectrum_le hP.isHermitian.isSelfAdjoint).mpr
    intro x hx
    rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hi j (Finset.mem_univ j)
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.le_iff.mp hb

lemma psd_slack_eigenvector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {r : ℝ} {v : ι → ℝ}
    (hS : (r • (1 : Matrix ι ι ℝ) - P).PosSemidef)
    (hq : r * dotProduct v v ≤ dotProduct v (P *ᵥ v)) : P *ᵥ v = r • v := by
  have hn := hS.re_dotProduct_nonneg v
  have heq : star v ⬝ᵥ ((r • (1 : Matrix ι ι ℝ) - P) *ᵥ v) = 0 := by
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, RCLike.re_to_real] at hn ⊢
    linarith
  have hz := (hS.dotProduct_mulVec_zero_iff v).mp heq
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm] using hz

lemma inverse_slack_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Matrix ι ι ℝ} (hJ : J.PosDef) {r : ℝ} (hr : 0 < r)
    (hS : (r • (1 : Matrix ι ι ℝ) - J⁻¹).PosSemidef) :
    (J - r⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hjp : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J ((Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit)
  have hb : algebraMap ℝ (Matrix ι ι ℝ) r⁻¹ ≤ J := by
    apply (algebraMap_le_iff_le_spectrum hJ.isHermitian.isSelfAdjoint).mpr
    intro x hx
    rw [hJ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    let ev := hJ.isHermitian.eigenvalues i
    let v : ι → ℝ := hJ.isHermitian.eigenvectorBasis i
    have hv : v ≠ 0 := by
      intro hz
      apply hJ.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
      ext j
      exact congrFun hz j
    have hev : 0 < ev := hJ.eigenvalues_pos i
    have heig : J *ᵥ v = ev • v := hJ.isHermitian.mulVec_eigenvectorBasis i
    have hp : J⁻¹ *ᵥ v = ev⁻¹ • v := by
      have h := congrArg (fun z => J⁻¹ *ᵥ z) heig
      rw [Matrix.mulVec_mulVec, hjp, Matrix.one_mulVec, Matrix.mulVec_smul] at h
      calc
        J⁻¹ *ᵥ v = ev⁻¹ • (ev • (J⁻¹ *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hev.ne', one_smul]
        _ = ev⁻¹ • v := by rw [← h]
    have hs := hS.re_dotProduct_nonneg v
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hp, dotProduct_sub, dotProduct_smul, smul_eq_mul, RCLike.re_to_real] at hs
    have hd : 0 < dotProduct v v := by simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hv)
    have hinv : ev⁻¹ ≤ r := by nlinarith
    change r⁻¹ ≤ ev
    exact (inv_le_comm₀ hr hev).mpr hinv
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.le_iff.mp hb

end NLA.SP05
