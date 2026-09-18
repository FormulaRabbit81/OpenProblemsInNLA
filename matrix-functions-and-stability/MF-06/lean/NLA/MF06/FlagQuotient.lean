/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

On a successive flag prefix, the concrete fiber projection is onto and its
kernel is precisely the preceding prefix. These exact statements identify
the diagonal block with the successive quotient, including zero fibers.
-/
import NLA.MF06.FlagCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma flagBlockProjection_zero_iff {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (i : Fin r) (x : EuclideanVector d) (hx : x ∈ F i.succ) :
    flagBlockProjection B b i x = 0 ↔ x ∈ F i.castSucc := by
  constructor
  · intro hz
    apply (mem_flag_iff_repr_zero F B b hspan i.castSucc x).mpr
    intro j hj
    by_cases he : b j = i
    · obtain ⟨u, hu⟩ := blockCoordinate_covers b i j he
      have hcoord := congrArg (fun v : EuclideanVector (blockDim b i) => v u) hz
      simpa only [flagBlockProjection_apply, hu, PiLp.zero_apply] using hcoord
    · apply (mem_flag_iff_repr_zero F B b hspan i.succ x).mp hx j
      have hne : (b j).val ≠ i.val := fun h => he (Fin.ext h)
      change i.val + 1 ≤ (b j).val
      change i.val ≤ (b j).val at hj
      omega
  · intro hxprev
    ext u
    change B.repr x (blockCoordinate b i u) = 0
    apply (mem_flag_iff_repr_zero F B b hspan i.castSucc x).mp hxprev
    rw [blockCoordinate_label b i u]
    exact le_rfl

lemma flagBlockProjection_surjective_on {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (i : Fin r) (z : EuclideanVector (blockDim b i)) :
    ∃ x : EuclideanVector d, x ∈ F i.succ ∧ flagBlockProjection B b i x = z := by
  classical
  let v : Fin d → ℂ := fun j =>
    if h : b j = i then z (Fintype.equivFin (BlockIndex b i) ⟨j, h⟩) else 0
  let x := B.equivFun.symm v
  have hrepr (j : Fin d) : B.repr x j = v j := by
    exact congrFun (B.equivFun.apply_symm_apply v) j
  refine ⟨x, ?_, ?_⟩
  · apply (mem_flag_iff_repr_zero F B b hspan i.succ x).mpr
    intro j hj
    rw [hrepr]
    have hne : b j ≠ i := by
      intro h
      rw [h] at hj
      exact Nat.not_succ_le_self i.val hj
    exact dif_neg hne
  · ext u
    rw [flagBlockProjection_apply, hrepr]
    dsimp only [v]
    rw [dif_pos (blockCoordinate_label b i u)]
    have he : (⟨blockCoordinate b i u, blockCoordinate_label b i u⟩ : BlockIndex b i) =
        (Fintype.equivFin (BlockIndex b i)).symm u := by rfl
    rw [he]
    exact congrArg (fun v : Fin (blockDim b i) => z v)
      ((Fintype.equivFin (BlockIndex b i)).apply_symm_apply u)

#print axioms flagBlockProjection_zero_iff
#assert_trust kernel flagBlockProjection_zero_iff
#print axioms flagBlockProjection_surjective_on
#assert_trust kernel flagBlockProjection_surjective_on

end NLA.MF06
