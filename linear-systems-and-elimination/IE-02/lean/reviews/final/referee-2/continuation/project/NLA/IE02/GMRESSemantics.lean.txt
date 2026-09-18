/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses the proved affine minima and exact polynomial residual parameterization.

Both GMRES infima are attained for every complex square matrix and every degree.
All norms are the frozen Euclidean norms; dimension and degree zero are retained.
-/
import NLA.IE02.PolynomialResiduals
import NLA.IE02.AffineMinima

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem gmres_extrema_semantics {n : ℕ} (A : Square n) (k : ℕ) :
    (∃ p : Poly, Admissible k p ∧ operatorNorm (polyEval p A) = idealGMRES A k ∧
      ∀ q : Poly, Admissible k q → operatorNorm (polyEval p A) ≤ operatorNorm (polyEval q A)) ∧
    (∀ x : H n, ∃ p : Poly, Admissible k p ∧
      ‖euclideanLin (polyEval p A) x‖ = gmresInner A k x ∧
      ∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p A) x‖ ≤
        ‖euclideanLin (polyEval q A) x‖) ∧
    (∀ x ∈ unitSphere n, 0 ≤ gmresInner A k x ∧ gmresInner A k x ≤ idealGMRES A k) := by
  let R : Fin k → Square n := fun j => A ^ (j.val + 1)
  -- These are equalities of the actual value sets in the frozen sInf definitions.
  have hideal : idealGMRES A k = affineIdeal (1 : Square n) R :=
    congrArg (sInf : Set ℝ → ℝ) (polynomial_residual_value_set A k operatorNorm)
  have hinner (x : H n) : gmresInner A k x = affineInner (1 : Square n) R x :=
    congrArg (sInf : Set ℝ → ℝ)
      (polynomial_residual_value_set A k (fun B => ‖euclideanLin B x‖))
  have hoperator : ∃ p : Poly, Admissible k p ∧
      operatorNorm (polyEval p A) = idealGMRES A k ∧
      ∀ q : Poly, Admissible k q → operatorNorm (polyEval p A) ≤ operatorNorm (polyEval q A) := by
    obtain ⟨c, hc, hcmin⟩ := affine_operator_minimum (1 : Square n) R
    obtain ⟨p, hp, heval⟩ := (polynomial_residual_parameterization A k).2 c
    refine ⟨p, hp, ?_, ?_⟩
    · rw [heval, hideal]
      exact hc
    · intro q hq
      obtain ⟨d, hd⟩ := (polynomial_residual_parameterization A k).1 q hq
      rw [heval, hd]
      exact hcmin d
  have hvector (x : H n) : ∃ p : Poly, Admissible k p ∧
      ‖euclideanLin (polyEval p A) x‖ = gmresInner A k x ∧
      ∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p A) x‖ ≤
        ‖euclideanLin (polyEval q A) x‖ := by
    obtain ⟨c, hc, hcmin⟩ := affine_vector_minimum (1 : Square n) R x
    obtain ⟨p, hp, heval⟩ := (polynomial_residual_parameterization A k).2 c
    refine ⟨p, hp, ?_, ?_⟩
    · rw [heval, hinner x]
      exact hc
    · intro q hq
      obtain ⟨d, hd⟩ := (polynomial_residual_parameterization A k).1 q hq
      rw [heval, hd]
      exact hcmin d
  refine ⟨hoperator, hvector, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ = 1 := hx
  obtain ⟨p, hp, hpvalue, _hpmin⟩ := hoperator
  obtain ⟨q, _hq, hqvalue, hqmin⟩ := hvector x
  constructor
  · rw [← hqvalue]
    exact norm_nonneg _
  · calc
      gmresInner A k x = ‖euclideanLin (polyEval q A) x‖ := hqvalue.symm
      _ ≤ ‖euclideanLin (polyEval p A) x‖ := hqmin p hp
      _ ≤ operatorNorm (polyEval p A) * ‖x‖ := (euclideanCLM (polyEval p A)).le_opNorm x
      _ = idealGMRES A k := by rw [hxnorm, mul_one, hpvalue]

#print axioms gmres_extrema_semantics
#assert_trust kernel gmres_extrema_semantics

end
end NLA.IE02
