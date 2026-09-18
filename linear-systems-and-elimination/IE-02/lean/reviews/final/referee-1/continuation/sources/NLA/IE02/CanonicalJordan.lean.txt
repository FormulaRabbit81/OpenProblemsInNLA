/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

The complete value sets are transported before taking infima or suprema.
Polynomial and vector witnesses then give all canonical attainment clauses.
The frozen nonzero eigenvalue and degree restrictions are retained literally;
the proved transport itself does not require those extra restrictions.
-/
import NLA.IE02.AffineMinimax
import NLA.IE02.JordanDirections
import NLA.IE02.JordanTransport
import NLA.IE02.GMRESSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

private theorem jordan_operator_transport (n : ℕ) (lam : ℂ) (p : Poly) :
    operatorNorm (polyEval p (jordan n lam)) =
      operatorNorm (polyEval p (lowerJordan n lam)) :=
  (jordan_polynomial_transport n lam p).2.1

private theorem jordan_vector_norm_transport (n : ℕ) (lam : ℂ) (p : Poly) (x : H n) :
    ‖euclideanLin (polyEval p (jordan n lam)) (reverseVector x)‖ =
      ‖euclideanLin (polyEval p (lowerJordan n lam)) x‖ := by
  rw [(jordan_polynomial_transport n lam p).2.2 x, reverseVector_norm]

private theorem jordan_affine_extrema (n k : ℕ) (lam : ℂ) :
    idealGMRES (jordan n lam) k = affineIdeal 1 (jordanDirections n k lam) ∧
    (∀ x : H n, gmresInner (jordan n lam) k (reverseVector x) =
      affineInner 1 (jordanDirections n k lam) x) ∧
    worstGMRES (jordan n lam) k = affineWorst 1 (jordanDirections n k lam) := by
  have hidealset :
      {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = operatorNorm (polyEval p (jordan n lam))} =
      {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = operatorNorm (polyEval p (lowerJordan n lam))} := by
    ext t
    simp only [jordan_operator_transport]
  have hideal : idealGMRES (jordan n lam) k = affineIdeal 1 (jordanDirections n k lam) :=
    (congrArg (sInf : Set ℝ → ℝ) hidealset).trans
      (congrArg (sInf : Set ℝ → ℝ)
        (polynomial_residual_value_set (lowerJordan n lam) k operatorNorm))
  have hinner (x : H n) : gmresInner (jordan n lam) k (reverseVector x) =
      affineInner 1 (jordanDirections n k lam) x := by
    have hvalues :
        {t : ℝ | ∃ p : Poly, Admissible k p ∧
          t = ‖euclideanLin (polyEval p (jordan n lam)) (reverseVector x)‖} =
        {t : ℝ | ∃ p : Poly, Admissible k p ∧
          t = ‖euclideanLin (polyEval p (lowerJordan n lam)) x‖} := by
      ext t
      simp only [jordan_vector_norm_transport]
    exact (congrArg (sInf : Set ℝ → ℝ) hvalues).trans
      (congrArg (sInf : Set ℝ → ℝ)
        (polynomial_residual_value_set (lowerJordan n lam) k (fun A => ‖euclideanLin A x‖)))
  have hunit (x : H n) : reverseVector x ∈ unitSphere n ↔ x ∈ unitSphere n := by
    simp only [unitSphere, Set.mem_ofPred_eq, reverseVector_norm]
  have hworstset : gmresInner (jordan n lam) k '' unitSphere n =
      affineInner 1 (jordanDirections n k lam) '' unitSphere n := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨reverseVector x, (hunit x).mpr hx, ?_⟩
      have h := hinner (reverseVector x)
      rw [reverseVector_involutive] at h
      exact h.symm
    · rintro ⟨x, hx, rfl⟩
      exact ⟨reverseVector x, (hunit x).mpr hx, hinner x⟩
  exact ⟨hideal, hinner, congrArg (sSup : Set ℝ → ℝ) hworstset⟩

theorem canonical_jordan_minimax (n k : ℕ) (lam : ℂ)
    (hn : 2 ≤ n) (hlam : lam ≠ 0) (hk : 1 ≤ k) (hkn : k < n) :
    worstGMRES (jordan n lam) k = idealGMRES (jordan n lam) k ∧
    (∀ x ∈ unitSphere n, ∃ p : Poly, Admissible k p ∧
      ‖euclideanLin (polyEval p (jordan n lam)) x‖ = gmresInner (jordan n lam) k x ∧
      ∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p (jordan n lam)) x‖ ≤
        ‖euclideanLin (polyEval q (jordan n lam)) x‖) ∧
    ∃ (p : Poly) (x : H n), Admissible k p ∧ x ∈ unitSphere n ∧
      operatorNorm (polyEval p (jordan n lam)) = idealGMRES (jordan n lam) k ∧
      ‖euclideanLin (polyEval p (jordan n lam)) x‖ = operatorNorm (polyEval p (jordan n lam)) ∧
      gmresInner (jordan n lam) k x = worstGMRES (jordan n lam) k ∧
      (∀ q : Poly, Admissible k q →
        operatorNorm (polyEval p (jordan n lam)) ≤ operatorNorm (polyEval q (jordan n lam))) ∧
      (∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p (jordan n lam)) x‖ ≤
        ‖euclideanLin (polyEval q (jordan n lam)) x‖) ∧
      (∀ z ∈ unitSphere n, gmresInner (jordan n lam) k z ≤ gmresInner (jordan n lam) k x) := by
  obtain ⟨hideal, hinner, hworst⟩ := jordan_affine_extrema n k lam
  obtain ⟨hI, hR⟩ := jordan_direction_toeplitz n k lam
  obtain ⟨hvalue, _hpointwise, c, x, hx, hc, hxinner, hnorm, hcmin, hxmin, hxmax⟩ :=
    affine_minimax_attained (by omega : 1 ≤ n) (1 : Square n) (jordanDirections n k lam) hI hR
  refine ⟨hworst.trans (hvalue.trans hideal.symm), ?_, ?_⟩
  · intro z _hz
    exact (gmres_extrema_semantics (jordan n lam) k).2.1 z
  · obtain ⟨p, hp, heval⟩ := (normalized_polynomial_residuals n k lam).2 c
    have hy : reverseVector x ∈ unitSphere n := by
      simpa only [unitSphere, Set.mem_ofPred_eq, reverseVector_norm] using hx
    refine ⟨p, reverseVector x, hp, hy, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [jordan_operator_transport, heval, hideal]
      exact hc
    · rw [jordan_vector_norm_transport, jordan_operator_transport, heval]
      exact hnorm
    · rw [hinner, hworst]
      exact hxinner
    · intro q hq
      obtain ⟨d, hd⟩ := (normalized_polynomial_residuals n k lam).1 q hq
      rw [jordan_operator_transport, jordan_operator_transport, heval, hd]
      exact hcmin d
    · intro q hq
      obtain ⟨d, hd⟩ := (normalized_polynomial_residuals n k lam).1 q hq
      rw [jordan_vector_norm_transport, jordan_vector_norm_transport, heval, hd]
      exact hxmin d
    · intro z hz
      have hzinner := hinner (reverseVector z)
      rw [reverseVector_involutive] at hzinner
      rw [hzinner, hinner]
      apply hxmax
      simpa only [unitSphere, Set.mem_ofPred_eq, reverseVector_norm] using hz

#print axioms canonical_jordan_minimax
#assert_trust kernel canonical_jordan_minimax

end
end NLA.IE02
