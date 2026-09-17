/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's finite tuple, polynomial coefficient and linear-equivalence APIs.

Finite coefficient lifting and the exact append/prefix maps for a Schur step.
No equality of finite Toeplitz matrices is promoted to polynomial equality.
-/
import NLA.IE02.SchurReduction

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

theorem toeplitz_X_lift {n : ℕ} (s t : Poly) (h : toeplitz n s = toeplitz n t) :
    toeplitz (n + 1) (X * s) = toeplitz (n + 1) (X * t) := by
  ext i j
  simp only [toeplitz]
  by_cases hji : j.val ≤ i.val
  · simp only [if_pos hji]
    cases he : i.val - j.val with
    | zero => simp only [Polynomial.coeff_X_mul_zero]
    | succ k =>
      have hk : k < n := by omega
      have hn : 0 < n := by omega
      have heq := congrArg (fun A : Square n => A ⟨k, hk⟩ ⟨0, hn⟩) h
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
      simpa only [toeplitz, Nat.zero_le, if_true, Nat.sub_zero] using heq
  · simp only [if_neg hji]

theorem schur_lift_interpolation {n : ℕ} (Z : Square (n + 1)) (a b : Poly)
    (hZ : IsToeplitz Z) (hdiag : ∀ i, Z i i = 0)
    (hinterp : activeBlock Z * toeplitz n b = toeplitz n a) :
    Z * toeplitz (n + 1) b = toeplitz (n + 1) (X * a) := by
  rcases hZ with ⟨q, rfl⟩
  have hq : q.coeff 0 = 0 := by
    simpa [toeplitz] using hdiag (0 : Fin (n + 1))
  have hsplit : q = X * q.divX := by
    simpa only [hq, Polynomial.C_0, add_zero] using (Polynomial.X_mul_divX_add q).symm
  have hsmall : toeplitz n (q.divX * b) = toeplitz n a := by
    rw [toeplitz_mul, ← activeBlock_toeplitz_divX n q hq]
    exact hinterp
  calc
    toeplitz (n + 1) q * toeplitz (n + 1) b = toeplitz (n + 1) (q * b) :=
      (toeplitz_mul _ _ _).symm
    _ = toeplitz (n + 1) ((X * q.divX) * b) :=
      congrArg (fun r : Poly => toeplitz (n + 1) (r * b)) hsplit
    _ = toeplitz (n + 1) (X * (q.divX * b)) := by rw [mul_assoc]
    _ = toeplitz (n + 1) (X * a) := toeplitz_X_lift _ _ hsmall

theorem schur_coeffVector_smul (n : ℕ) (c : ℂ) (p : Poly) :
    coeffVector n (c • p) = c • coeffVector n p := by
  apply PiLp.ext
  intro i
  simp [coeffVector]

theorem schur_coeffVector_append {n : ℕ} (p : Poly) (hp : DegreeLE p n) :
    coeffVector (n + 2) p = appendVector (coeffVector (n + 1) p) 0 := by
  have hlast : p.coeff (n + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hp.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)))
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [coeffVector, appendVector, hlast]
  · simp [coeffVector, appendVector]

/-- The coordinate inclusion appends a literal zero, retaining the Euclidean space. -/
def schurAppendLinear (n : ℕ) : H n →ₗ[ℂ] H (n + 1) where
  toFun g := appendVector g 0
  map_add' g h := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [appendVector]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [appendVector]

/-- Projection onto the first n coordinates; no normed-space identification is changed. -/
def schurPrefixLinear (n : ℕ) : H (n + 1) →ₗ[ℂ] H n where
  toFun y := WithLp.toLp 2 (fun i => y i.castSucc)
  map_add' y z := by
    apply PiLp.ext
    intro i
    rfl
  map_smul' c y := by
    apply PiLp.ext
    intro i
    rfl

theorem schur_prefix_append {n : ℕ} (g : H n) (η : ℂ) :
    schurPrefixLinear n (appendVector g η) = g := by
  apply PiLp.ext
  intro i
  simp [schurPrefixLinear, appendVector]

theorem schur_maximal_append {n : ℕ} (Z : Square (n + 1))
    (hZ : IsToeplitz Z) (hdiag : ∀ i, Z i i = 0)
    (hZnorm : operatorNorm Z = 1) (hVnorm : operatorNorm (activeBlock Z) = 1)
    (g : H n) (η : ℂ) :
    appendVector g η ∈ maximalSpace Z ↔ η = 0 ∧ g ∈ maximalSpace (activeBlock Z) := by
  rw [maximal_space_norm_one Z hZnorm,
    maximal_space_norm_one (activeBlock Z) hVnorm]
  exact ((schur_active_block Z hZ hdiag hZnorm.le).2.2 g η).2.2

theorem schur_maximal_prefix {n : ℕ} (Z : Square (n + 1))
    (hZ : IsToeplitz Z) (hdiag : ∀ i, Z i i = 0)
    (hZnorm : operatorNorm Z = 1) (hVnorm : operatorNorm (activeBlock Z) = 1)
    (y : H (n + 1)) :
    y ∈ maximalSpace Z ↔
      y = appendVector (schurPrefixLinear n y) 0 ∧
      schurPrefixLinear n y ∈ maximalSpace (activeBlock Z) := by
  obtain ⟨g, η, rfl⟩ := exists_appendVector y
  rw [schur_prefix_append, schur_maximal_append Z hZ hdiag hZnorm hVnorm]
  constructor
  · rintro ⟨rfl, hg⟩
    exact ⟨rfl, hg⟩
  · rintro ⟨heq, hg⟩
    refine ⟨?_, hg⟩
    simpa only [appendVector, PiLp.toLp_apply, Fin.snoc_last] using
      congrArg (fun x : H (n + 1) => x (Fin.last n)) heq

theorem schur_maximal_finrank {n : ℕ} (U Z M B : Square (n + 1))
    (hleft : M * B = 1) (hright : B * M = 1)
    (hZ : IsToeplitz Z) (hdiag : ∀ i, Z i i = 0)
    (hZnorm : operatorNorm Z = 1) (hVnorm : operatorNorm (activeBlock Z) = 1)
    (htransport : ∀ x, x ∈ maximalSpace U ↔ euclideanLin M x ∈ maximalSpace Z) :
    Module.finrank ℂ (maximalSpace U) = Module.finrank ℂ (maximalSpace (activeBlock Z)) := by
  let f := (schurPrefixLinear n).comp (euclideanLin M)
  let g := (euclideanLin B).comp (schurAppendLinear n)
  have hf : ∀ x ∈ maximalSpace U, f x ∈ maximalSpace (activeBlock Z) := by
    intro x hx
    exact ((schur_maximal_prefix Z hZ hdiag hZnorm hVnorm _).mp ((htransport x).mp hx)).2
  have hg : ∀ x ∈ maximalSpace (activeBlock Z), g x ∈ maximalSpace U := by
    intro x hx
    apply (htransport _).mpr
    -- Expose the composed linear maps so the supplied left inverse cancels.
    change euclideanLin M (euclideanLin B (appendVector x 0)) ∈ maximalSpace Z
    rw [← euclideanLin_mul_apply, hleft, euclideanLin_one_apply]
    exact (schur_maximal_append Z hZ hdiag hZnorm hVnorm x 0).mpr ⟨rfl, hx⟩
  let F := f.restrict hf
  let G := g.restrict hg
  have hFG : F.comp G = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    -- The restricted maps use exactly prefix(M(B(append x 0))).
    change schurPrefixLinear n (euclideanLin M (euclideanLin B (appendVector (x : H n) 0))) = x
    rw [← euclideanLin_mul_apply, hleft, euclideanLin_one_apply, schur_prefix_append]
  have hGF : G.comp F = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    -- Expose B(append(prefix(Mx),0)) from the restricted maps; prefix recovery gives Mx.
    change euclideanLin B (appendVector (schurPrefixLinear n (euclideanLin M x)) 0) = x
    have heq := ((schur_maximal_prefix Z hZ hdiag hZnorm hVnorm _).mp
      ((htransport (x : H (n + 1))).mp x.property)).1
    rw [← heq, ← euclideanLin_mul_apply, hright, euclideanLin_one_apply]
  exact (LinearEquiv.ofLinearMap F G hFG hGF).finrank_eq

#print axioms schur_lift_interpolation
#assert_trust kernel schur_lift_interpolation
#print axioms schur_maximal_finrank
#assert_trust kernel schur_maximal_finrank

end
end NLA.IE02
