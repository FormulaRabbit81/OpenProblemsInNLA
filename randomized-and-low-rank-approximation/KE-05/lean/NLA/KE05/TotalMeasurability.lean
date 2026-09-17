import NLA.KE05.Measurability
import NLA.KE05.GenericValidity

/- Finite extrema and the prescribed endpoint convention remain measurable on
all samples. No exceptional event is discarded in the measurable function. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.KE05
local instance matrixMeasurableSpaceTotal (b : ℕ) : MeasurableSpace (Mat b) :=
  inferInstanceAs (MeasurableSpace (Fin b → Fin b → ℝ))

lemma measurable_endpointRatio {α : Type*} [MeasurableSpace α] {b : ℕ}
    (t : ℝ) (H : α → Mat b) (D : Mat b)
    (hH : ∀ i j, Measurable (fun x => H x i j)) :
    Measurable (fun x => endpointRatio t (H x) D) := by
  have hn : Measurable (fun x => spectralNorm (t • (1 : Mat b) - H x)) :=
    measurable_spectralNorm.comp (measurable_matrix_of_entries _ (fun i j => measurable_const.sub (hH i j)))
  have hp : MeasurableSet {x | spectralNorm (t • (1 : Mat b) - H x) = 0 ∧
      spectralNorm (t • (1 : Mat b) - D) = 0} := by
    apply (measurableSet_eq_fun hn measurable_const).inter
    exact measurable_const.setOf
  exact Measurable.ite hp measurable_const (hn.div_const _)

lemma measurable_monoOrdering {b d : ℕ} (L : Data b d) (hL : Admissible L) (k : Fin d) :
    Measurable (fun w => monoOrdering L w k) := by
  let f : ({i : Fin d // 1 ≤ i.val} × Bool) → Sample b d → ℝ := fun p w =>
    if p.2 then endpointRatio (upperEndpoint L) ((recurrence L w k).hat p.1.val)
        (Matrix.diagonal (L (rootOrder k p.1.val)))
    else endpointRatio (lowerEndpoint L) ((recurrence L w k).hat p.1.val)
        (Matrix.diagonal (L (rootOrder k p.1.val)))
  have hf : ∀ p, Measurable (f p) := by
    intro p
    rcases p with ⟨i,t⟩
    cases t <;> exact measurable_endpointRatio _ _ _ (recurrence_hat_measurable L hL k i.val)
  have he (w : Sample b d) :
      {x | ∃ i : Fin d, 1 ≤ i.val ∧
        (x = endpointRatio (lowerEndpoint L) ((recurrence L w k).hat i)
          (Matrix.diagonal (L (rootOrder k i))) ∨
         x = endpointRatio (upperEndpoint L) ((recurrence L w k).hat i)
          (Matrix.diagonal (L (rootOrder k i))))} = Set.range (fun p => f p w) := by
    ext x
    constructor
    · rintro ⟨i,hi,h | h⟩
      · exact ⟨(⟨i,hi⟩,false),h.symm⟩
      · exact ⟨(⟨i,hi⟩,true),h.symm⟩
    · rintro ⟨⟨i,t⟩,rfl⟩
      refine ⟨i.val,i.property,?_⟩
      cases t <;> simp [f]
  unfold monoOrdering
  simp_rw [he]
  exact measurable_const.max (Measurable.iSup hf)

lemma measurable_coefOrdering {b d : ℕ} (L : Data b d) (hL : Admissible L) (k : Fin d) :
    Measurable (fun w => coefOrdering L w k) := by
  have hn : Measurable (fun w => spectralNorm ((recurrence L w k).lastS (firstPosition k))⁻¹) :=
    measurable_spectralNorm.comp (measurable_matrix_of_entries _
      (measurable_matrix_inverse _ (recurrence_lastS_measurable L hL k (firstPosition k))))
  exact (hn.pow_const (1 / ((d-1 : ℕ) : ℝ))).mul_const (crossGap L k)

lemma measurable_valid {b d : ℕ} (L : Data b d) (hL : Admissible L) :
    MeasurableSet {w | Valid L w} := by
  have ho : Measurable (fun w : Sample b d => ∀ i, (omega w i).det ≠ 0) :=
    Measurable.forall fun i => measurableSet_setOfPred.mp
      ((measurableSet_eq_fun (measurable_matrix_det _ (fun r c => measurable_pi_apply (i,r,c)))
        measurable_const).compl)
  have hs : Measurable (fun w : Sample b d => ∀ k i,
      (omega w (rootOrder k i) * (recurrence L w k).lastS i).det ≠ 0) := by
    apply Measurable.forall
    intro k
    apply Measurable.forall
    intro i
    have h1 := measurable_matrix_det (fun w : Sample b d => omega w (rootOrder k i))
      (fun r c => measurable_pi_apply (rootOrder k i,r,c))
    have h2 := measurable_matrix_det _ (recurrence_lastS_measurable L hL k i)
    apply measurableSet_setOfPred.mp
    simpa only [Matrix.det_mul, Pi.mul_apply, Set.compl_setOf] using (measurableSet_eq_fun (h1.mul h2) measurable_const).compl
  exact (ho.and hs).setOf

lemma measurable_totalConstant {b d : ℕ} (L : Data b d) (hL : Admissible L) :
    Measurable (totalConstant L) := by
  have hm : Measurable (mono L) := Measurable.iSup (measurable_monoOrdering L hL)
  have hc : Measurable (coef L) := Measurable.iSup (measurable_coefOrdering L hL)
  exact Measurable.ite (measurable_valid L hL) (hm.mul hc) measurable_const

 theorem probability_one_validity_proved {b d : ℕ} (_hb : 1 ≤ b) (_hd : 2 ≤ d)
    (L : Data b d) (hL : Admissible L) :
    (∀ᵐ w ∂gaussianLaw b d, Valid L w) ∧ Measurable (totalConstant L) :=
  ⟨all_orderings_valid_ae L hL, measurable_totalConstant L hL⟩

end NLA.KE05
