/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Actual inverse columns and Sidney Holden's attributed IV-03 maximum principle
give the componentwise resolvent inequality without expanding an inverse.
-/
import NLA.SF01.AbsoluteComparison
import NLA.SF01.WeightedZReuse

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped Matrix

lemma inverse_mulVec_column {n : ℕ} (C : Square n) (hC : IsUnit C)
    (j : Fin n) : C *ᵥ (fun k => C⁻¹ k j) = (fun i => (1 : Square n) i j) := by
  funext i
  change (C * C⁻¹) i j = (1 : Square n) i j
  rw [Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC)]

lemma abs_identity_entry {n : ℕ} (i j : Fin n) :
    |(1 : Square n) i j| = (1 : Square n) i j := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem resolvent_domination {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : Admissible A) (t : ℝ) (ht : 0 ≤ t) :
    IsUnit (shifted A t) ∧ IsUnit (shifted (comparison A) t) ∧
      ∀ i j, |((shifted A t)⁻¹) i j| ≤ ((shifted (comparison A) t)⁻¹) i j := by
  have hshift := H_shift_structure hn A hA t ht
  have hZ : IsZMatrix (shifted (comparison A) t) := shifted_isZ _ (comparison_isZ A) t
  have hC : IsUnit (shifted (comparison A) t) :=
    weightedZ_isUnit _ (weightVector (comparison A)) hZ hshift.2.2
  refine ⟨hshift.2.1, hC, ?_⟩
  intro i j
  have hbound : ∀ l,
      (shifted (comparison A) t *ᵥ (fun k => |((shifted A t)⁻¹) k j|)) l ≤
        (1 : Square n) l j := by
    intro l
    have h := comparison_abs_mulVec A hA.2 t ht (fun k => ((shifted A t)⁻¹) k j) l
    rw [inverse_mulVec_column (shifted A t) hshift.2.1 j, abs_identity_entry] at h
    exact h
  have hnonneg : ∀ l, 0 ≤
      (shifted (comparison A) t *ᵥ
        ((fun k => ((shifted (comparison A) t)⁻¹) k j) -
          (fun k => |((shifted A t)⁻¹) k j|))) l := by
    intro l
    rw [Matrix.mulVec_sub, inverse_mulVec_column (shifted (comparison A) t) hC j]
    change 0 ≤ (1 : Square n) l j -
      (shifted (comparison A) t *ᵥ (fun k => |((shifted A t)⁻¹) k j|)) l
    exact sub_nonneg.mpr (hbound l)
  have h := weightedZ_maximum_principle (shifted (comparison A) t)
    (weightVector (comparison A))
    ((fun k => ((shifted (comparison A) t)⁻¹) k j) -
      (fun k => |((shifted A t)⁻¹) k j|)) hZ hshift.2.2 hnonneg i
  exact sub_nonneg.mp h

end
end NLA.SF01
