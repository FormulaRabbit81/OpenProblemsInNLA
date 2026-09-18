/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The limit descends to the actual Mathlib quotient by its actual kernel. Its
bundled quotient seminorm is definite. The quotient evaluation identity then
proves invariance under subtracting any kernel vector; this is the identity
used in the later complement and off-diagonal estimates.
-/
import NLA.MF06.StableKernel
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma stableGauge_eq_of_sub_mem {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x y : EuclideanVector d) (hxy : x - y ∈ stableKernel M hM hneM hbounded) :
    stableGauge M x = stableGauge M y := by
  have hzero : stableGauge M (x - y) = 0 := hxy
  have hbound := (stableSeminorm M hM hneM hbounded).norm_sub_map_le_sub x y
  have hnorm : ‖stableGauge M x - stableGauge M y‖ = 0 :=
    le_antisymm (hbound.trans_eq hzero) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

def stableQuotientGauge {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    (EuclideanVector d ⧸ stableKernel M hM hneM hbounded) → ℝ :=
  Quotient.lift (stableGauge M) (fun x y hxy =>
    stableGauge_eq_of_sub_mem M hM hneM hbounded x y
      ((Submodule.quotientRel_def (stableKernel M hM hneM hbounded)).mp hxy))

@[simp] lemma stableQuotientGauge_mk {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    stableQuotientGauge M hM hneM hbounded (Submodule.Quotient.mk x) = stableGauge M x := rfl

/-- The actual quotient seminorm, with triangle and homogeneity descended from p. -/
def stableQuotientSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    Seminorm ℂ (EuclideanVector d ⧸ stableKernel M hM hneM hbounded) := by
  refine Seminorm.of (stableQuotientGauge M hM hneM hbounded) ?_ ?_
  · intro ξ η
    refine Submodule.Quotient.induction_on (stableKernel M hM hneM hbounded) ξ ?_
    intro x
    refine Submodule.Quotient.induction_on (stableKernel M hM hneM hbounded) η ?_
    intro y
    simpa only [← Submodule.Quotient.mk_add, stableQuotientGauge_mk] using
      stableGauge_triangle M hM hneM hbounded x y
  · intro c ξ
    refine Submodule.Quotient.induction_on (stableKernel M hM hneM hbounded) ξ ?_
    intro x
    simpa only [← Submodule.Quotient.mk_smul, stableQuotientGauge_mk] using
      stableGauge_smul M hM hneM hbounded c x

@[simp] lemma stableQuotientSeminorm_mk {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    stableQuotientSeminorm M hM hneM hbounded (Submodule.Quotient.mk x) = stableGauge M x := rfl

lemma stableQuotientSeminorm_definite {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (ξ : EuclideanVector d ⧸ stableKernel M hM hneM hbounded) :
    stableQuotientSeminorm M hM hneM hbounded ξ = 0 ↔ ξ = 0 := by
  refine Submodule.Quotient.induction_on (stableKernel M hM hneM hbounded) ξ ?_
  intro x
  rw [stableQuotientSeminorm_mk, Submodule.Quotient.mk_eq_zero, mem_stableKernel]

lemma stableGauge_sub_kernel {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x s : EuclideanVector d) (hs : s ∈ stableKernel M hM hneM hbounded) :
    stableGauge M (x - s) = stableGauge M x := by
  have hclass : (Submodule.Quotient.mk (x - s) :
      EuclideanVector d ⧸ stableKernel M hM hneM hbounded) = Submodule.Quotient.mk x := by
    apply (Submodule.Quotient.eq (stableKernel M hM hneM hbounded)).mpr
    have hsub : x - s - x = -s := by abel
    rw [hsub]
    exact (stableKernel M hM hneM hbounded).neg_mem hs
  simpa only [stableQuotientSeminorm_mk] using
    congrArg (stableQuotientSeminorm M hM hneM hbounded) hclass

lemma stableQuotient_nontrivial {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (hproper : stableKernel M hM hneM hbounded ≠ ⊤) :
    Nontrivial (EuclideanVector d ⧸ stableKernel M hM hneM hbounded) :=
  (Submodule.Quotient.nontrivial_iff (p := stableKernel M hM hneM hbounded)).mpr hproper

#print axioms stableQuotientSeminorm_definite
#assert_trust kernel stableQuotientSeminorm_definite
#print axioms stableGauge_sub_kernel
#assert_trust kernel stableGauge_sub_kernel

end NLA.MF06
