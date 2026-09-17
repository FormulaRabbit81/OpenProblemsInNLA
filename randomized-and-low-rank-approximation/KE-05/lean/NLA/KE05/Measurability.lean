import NLA.KE05.Definitions

/- Measurability of the actual totalized expressions, including singular inputs. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.KE05

local instance matrixMeasurableSpace (b : ℕ) : MeasurableSpace (Mat b) :=
  inferInstanceAs (MeasurableSpace (Fin b → Fin b → ℝ))
local instance matrixBorelSpace (b : ℕ) : BorelSpace (Mat b) :=
  inferInstanceAs (BorelSpace (Fin b → Fin b → ℝ))

lemma measurable_matrix_of_entries {α : Type*} [MeasurableSpace α] {b : ℕ}
    (A : α → Mat b) (hA : ∀ i j, Measurable (fun x => A x i j)) : Measurable A :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (hA i))

lemma measurable_spectralNorm {b : ℕ} : Measurable (spectralNorm (b := b)) := by
  have hc : Continuous (fun A : Mat b => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin b) A) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin b)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hc.norm.measurable

lemma measurable_matrix_det {α : Type*} [MeasurableSpace α] {b : ℕ}
    (A : α → Mat b) (hA : ∀ i j, Measurable (fun x => A x i j)) :
    Measurable (fun x => (A x).det) := by
  exact (continuous_id.matrix_det : Continuous (fun A : Mat b => A.det)).measurable.comp
    (measurable_matrix_of_entries A hA)

lemma measurable_matrix_inverse {α : Type*} [MeasurableSpace α] {b : ℕ}
    (A : α → Mat b) (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin b) :
    Measurable (fun x => (A x)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  apply Measurable.mul ((measurable_matrix_det A hA).inv)
  apply measurable_matrix_det
  intro r c
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact measurable_const
  · simp only [Matrix.updateRow_ne hr]
    exact hA r c

end NLA.KE05
