/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Single-column cofactor forms and their signed Laplace expansions.
-/
import NLA.NM04.CofactorSigned
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w
variable {α : Type u} {β : Type v} {𝕜 : Type w}
variable [LinearOrder α] [LinearOrder β] [CommRing 𝕜]

/-- The actual cofactor form in a direction supported in one selected column. -/
def minorColumnForm (T : Matrix α β 𝕜) (I : MinorIndex α β) (c : I.1.2)
    (x : α → 𝕜) : 𝕜 :=
  cofactorForm T I (fun r t => if t = (c : β) then x r else 0)

/-- C20 reduces a supported direction to the signed erased-minor column sum. -/
theorem minorColumnForm_signed (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (c : I.1.2) (x : α → 𝕜) :
    minorColumnForm T I c x = ∑ r : I.1.1,
      (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (c : β) I.1.2) *
        x r * minor T (erasedIndex I r c) := by
  calc
    _ = ∑ r : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (t : β) I.1.2) *
          (if (t : β) = c then x r else 0) * minor T (erasedIndex I r t) :=
      cofactor_signed_minor_formula T (fun r t => if t = (c : β) then x r else 0) I
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      refine (Finset.sum_eq_single_of_mem c (Finset.mem_univ c) ?_).trans ?_
      · intro t _ htc
        have hne : (t : β) ≠ c := fun h => htc (Subtype.ext h)
        simp only [if_neg hne, mul_zero, zero_mul]
      · simp only [ite_true]

/-- Increasing enumeration turns the supported cofactor into one adjugate row. -/
theorem minorColumnForm_adjugate (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (c : I.1.2) (x : α → 𝕜) :
    minorColumnForm T I c x = ∑ i : Fin I.1.1.card,
      (minorMatrix T I).adjugate ((I.1.2.orderIsoOfFin I.property.symm).symm c) i *
        x (I.1.1.orderEmbOfFin rfl i) := by
  let e := I.1.2.orderIsoOfFin I.property.symm
  let j := e.symm c
  have hc : I.1.2.orderEmbOfFin I.property.symm j = (c : β) :=
    congrArg Subtype.val (e.apply_symm_apply c)
  change (∑ i : Fin I.1.1.card, ∑ l : Fin I.1.1.card,
      (minorMatrix T I).adjugate l i *
        (if I.1.2.orderEmbOfFin I.property.symm l = (c : β) then
          x (I.1.1.orderEmbOfFin rfl i) else 0)) =
    ∑ i : Fin I.1.1.card, (minorMatrix T I).adjugate j i *
      x (I.1.1.orderEmbOfFin rfl i)
  apply Finset.sum_congr rfl
  intro i _
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro l _ hlj
    have hne : I.1.2.orderEmbOfFin I.property.symm l ≠ (c : β) := by
      intro heq
      exact hlj (e.injective (Subtype.ext (heq.trans hc.symm)))
    simp only [if_neg hne, mul_zero]
  · simp only [if_pos hc]

/-- Cramer's polynomial identity identifies this form with column replacement. -/
theorem minorColumnForm_eq_det_updateCol (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (c : I.1.2) (x : α → 𝕜) :
    minorColumnForm T I c x =
      ((minorMatrix T I).updateCol ((I.1.2.orderIsoOfFin I.property.symm).symm c)
        (fun i => x (I.1.1.orderEmbOfFin rfl i))).det := by
  let A := minorMatrix T I
  let v : Fin I.1.1.card → 𝕜 := fun i => x (I.1.1.orderEmbOfFin rfl i)
  let j := (I.1.2.orderIsoOfFin I.property.symm).symm c
  calc
    _ = ∑ i : Fin I.1.1.card, A.adjugate j i * v i :=
      minorColumnForm_adjugate T I c x
    _ = (Matrix.cramer A v) j :=
      (congrFun (Matrix.cramer_eq_adjugate_mulVec A v) j).symm
    _ = (A.updateCol j v).det := Matrix.cramer_apply A v j

/-- An existing selected column either leaves the determinant unchanged or
creates two equal columns. No invertibility assumption is needed. -/
theorem minorColumnForm_selected (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (c d : I.1.2) :
    minorColumnForm T I c (fun r => T r d) = if d = c then minor T I else 0 := by
  let A := minorMatrix T I
  let e := I.1.2.orderIsoOfFin I.property.symm
  let j := e.symm c
  let l := e.symm d
  have hd : I.1.2.orderEmbOfFin I.property.symm l = (d : β) :=
    congrArg Subtype.val (e.apply_symm_apply d)
  have hv : (fun i => T (I.1.1.orderEmbOfFin rfl i) d) =
      (fun i => A i l) := by
    funext i
    exact congrArg (fun t => T (I.1.1.orderEmbOfFin rfl i) t) hd.symm
  have hdet : minorColumnForm T I c (fun r => T r d) =
      (A.updateCol j (fun i => A i l)).det :=
    (minorColumnForm_eq_det_updateCol T I c (fun r => T r d)).trans
      (congrArg (fun v : Fin I.1.1.card → 𝕜 => (A.updateCol j v).det) hv)
  by_cases hdc : d = c
  · have hlj : l = j := congrArg e.symm hdc
    calc
      _ = (A.updateCol j (fun i => A i l)).det := hdet
      _ = (A.updateCol j (fun i => A i j)).det :=
        congrArg (fun q : Fin I.1.1.card => (A.updateCol j (fun i => A i q)).det) hlj
      _ = minor T I := congrArg
        (fun M : Matrix (Fin I.1.1.card) (Fin I.1.1.card) 𝕜 => M.det)
        (Matrix.updateCol_eq_self A j)
      _ = _ := (if_pos hdc).symm
  · have hlj : l ≠ j := fun h => hdc (e.symm.injective h)
    calc
      _ = (A.updateCol j (fun i => A i l)).det := hdet
      _ = 0 := Matrix.det_updateCol_eq_zero hlj
      _ = _ := (if_neg hdc).symm

/-- Signed Laplace expansion in a selected column, in the frozen set ordering. -/
theorem minor_laplace_column (T : Matrix α β 𝕜) (I : MinorIndex α β) (c : I.1.2) :
    minor T I = ∑ r : I.1.1,
      (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (c : β) I.1.2) *
        T r c * minor T (erasedIndex I r c) := by
  have hself : minorColumnForm T I c (fun r => T r c) = minor T I :=
    (minorColumnForm_selected T I c c).trans (if_pos rfl)
  exact hself.symm.trans (minorColumnForm_signed T I c (fun r => T r c))

#print axioms minorColumnForm_signed
#assert_trust kernel minorColumnForm_signed
#print axioms minorColumnForm_adjugate
#assert_trust kernel minorColumnForm_adjugate
#print axioms minorColumnForm_eq_det_updateCol
#assert_trust kernel minorColumnForm_eq_det_updateCol
#print axioms minorColumnForm_selected
#assert_trust kernel minorColumnForm_selected
#print axioms minor_laplace_column
#assert_trust kernel minor_laplace_column

end
end NLA.NM04
