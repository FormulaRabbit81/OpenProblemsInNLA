/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

This algebraic substitute for an adjugate derivative argument uses only
maximal generalized eigenspace dimension and the full primary decomposition.
-/
import NLA.MF18.StableKernel
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem eigenfunctional_shift_power {n : ℕ} (S : Mat n) (lam μ : ℂ)
    (f : Vec n →ₗ[ℂ] ℂ) (hf : ∀ w, f (S.mulVec w) = lam * f w) (k : ℕ) (w : Vec n) :
    f (((S - μ • (1 : Mat n)) ^ k).mulVec w) = (lam - μ) ^ k * f w := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_mulVec, one_mul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, map_sub, map_smul, hf, ih, smul_eq_mul,
      pow_succ]
    ring

theorem eigenfunctional_annihilates_other {n : ℕ} (S : Mat n) (lam μ : ℂ)
    (f : Vec n →ₗ[ℂ] ℂ) (hf : ∀ w, f (S.mulVec w) = lam * f w) (hne : lam ≠ μ)
    (w : Vec n) (hw : w ∈ (Module.End.maxGenEigenspace S.toLin') μ) : f w = 0 := by
  obtain ⟨k, hk⟩ := maxGenEigenspace_matrix_annihilation S μ w hw
  have he := congrArg f hk
  rw [eigenfunctional_shift_power S lam μ f hf, map_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hne))

theorem simple_eigenfunctional_nonzero {n : ℕ} (S : Mat n) (lam : ℂ)
    (hsimple : S.charpoly.rootMultiplicity lam = 1)
    (v : Vec n) (hv : v ≠ 0) (heig : S.mulVec v = lam • v)
    (f : Vec n →ₗ[ℂ] ℂ) (hfne : f ≠ 0)
    (hf : ∀ w, f (S.mulVec w) = lam * f w) : f v ≠ 0 := by
  have hvgen : v ∈ (Module.End.maxGenEigenspace S.toLin') lam := by
    apply (Module.End.mem_maxGenEigenspace S.toLin' lam v).mpr
    refine ⟨1, ?_⟩
    simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, Matrix.toLin'_apply, heig, sub_self]
  have hdim : Module.finrank ℂ ((Module.End.maxGenEigenspace S.toLin') lam) = 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hsimple]
  have hspan : (Module.End.maxGenEigenspace S.toLin') lam = Submodule.span ℂ {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hvgen hv
  intro hz
  have htop : (⊤ : Submodule ℂ (Vec n)) ≤ LinearMap.ker f := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top S.toLin']
    apply iSup_le
    intro μ
    by_cases hμ : μ = lam
    · rw [hμ, hspan]
      apply Submodule.span_le.mpr
      intro w hw
      have hwv : w = v := Set.mem_singleton_iff.mp hw
      subst w
      exact hz
    · intro w hw
      exact eigenfunctional_annihilates_other S lam μ f hf (Ne.symm hμ) w hw
  have hfzero : f = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp htop)
  exact hfne hfzero

#print axioms simple_eigenfunctional_nonzero

end NLA.MF18
