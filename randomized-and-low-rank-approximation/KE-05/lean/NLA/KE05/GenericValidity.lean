import NLA.KE05.RegularRecurrence
import NLA.KE05.RecurrenceUnique

/- Every prescribed ordering is defined almost surely for every admissible real
input. The result is about the literal zero-initialized recurrence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.KE05

lemma goodState_recurrence {b d : ℕ} (L : Data b d) (hL : Admissible L) (k : Fin d) :
    GoodState L k (fun w => recurrence L w k) := by
  have h := goodState_fold L hL k (List.finRange d).reverse (fun _ => convenientState L k)
    (goodState_initial L k)
  simpa only [recurrence_initial_independent] using h

lemma omega_nonsingular_ae {b d : ℕ} (i : Fin d) :
    ∀ᵐ w ∂gaussianLaw b d, (omega w i).det ≠ 0 := by
  have h := regular_matrix_det (fun w => omega w i) (regular_omega (identitySample b d) i)
  exact h.ae_ne_zero (by rw [omega_identity]; norm_num)

lemma recurrence_lastS_nonsingular_ae {b d : ℕ} (L : Data b d) (hL : Admissible L)
    (k i : Fin d) : ∀ᵐ w ∂gaussianLaw b d, ((recurrence L w k).lastS i).det ≠ 0 := by
  have hst := goodState_recurrence L hL k
  exact (regular_matrix_det (fun w => (recurrence L w k).lastS i)
    (hst.last_regular i)).ae_ne_zero (hst.last_det_identity i)

lemma all_orderings_valid_ae {b d : ℕ} (L : Data b d) (hL : Admissible L) :
    ∀ᵐ w ∂gaussianLaw b d, Valid L w := by
  have ho : ∀ᵐ w ∂gaussianLaw b d, ∀ i, (omega w i).det ≠ 0 :=
    (ae_all_iff).mpr (fun i => omega_nonsingular_ae i)
  have hs : ∀ᵐ w ∂gaussianLaw b d, ∀ k i, ((recurrence L w k).lastS i).det ≠ 0 :=
    (ae_all_iff).mpr (fun k => (ae_all_iff).mpr (fun i => recurrence_lastS_nonsingular_ae L hL k i))
  filter_upwards [ho,hs] with w hO hS
  refine ⟨hO, ?_⟩
  intro k i
  rw [Matrix.det_mul]
  exact mul_ne_zero (hO _) (hS k i)

lemma recurrence_hat_measurable {b d : ℕ} (L : Data b d) (hL : Admissible L)
    (k i : Fin d) (r c : Fin b) : Measurable (fun w => (recurrence L w k).hat i r c) :=
  ((goodState_recurrence L hL k).hat_regular i r c).measurable

lemma recurrence_lastS_measurable {b d : ℕ} (L : Data b d) (hL : Admissible L)
    (k i : Fin d) (r c : Fin b) : Measurable (fun w => (recurrence L w k).lastS i r c) :=
  ((goodState_recurrence L hL k).last_regular i r c).measurable

end NLA.KE05
