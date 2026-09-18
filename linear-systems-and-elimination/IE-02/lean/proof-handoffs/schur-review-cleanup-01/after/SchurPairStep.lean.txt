/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's matrix scalar algebra and the proved finite Schur helpers.

One complete Schur step, retaining the supplied inverse, all eleven SchurPair
clauses, the full maximal subspace and its dimension. The symbol p is arbitrary.
-/
import NLA.IE02.SchurPolynomial
import NLA.IE02.SchurCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

private theorem schur_step_matrix_interpolation {n : ℕ} (p a b : Poly)
    (B : Square n) (hleft : schurM (toeplitz n p) (p.coeff 0) * B = 1)
    (hlift : schurZ (toeplitz n p) (p.coeff 0) B * toeplitz n b = toeplitz n (X * a)) :
    toeplitz n p * toeplitz n (schurDenominator (p.coeff 0) a b) =
      toeplitz n (schurNumerator (p.coeff 0) a b) := by
  let U := toeplitz n p
  let c := p.coeff 0
  let M := schurM U c
  let Z := schurZ U c B
  have hM : IsToeplitz M := by
    refine ⟨1 - star c • p, ?_⟩
    simp only [toeplitz_sub, toeplitz_one, toeplitz_smul, M, schurM, U]
  have hW : IsToeplitz (U - c • 1) := by
    refine ⟨p - C c, ?_⟩
    simp only [toeplitz_sub, toeplitz_C, U]
  have hMZ : M * Z = U - c • 1 := by
    -- Only Toeplitz polynomial factors commute; no adjoint commutation is used.
    change M * ((U - c • 1) * B) = U - c • 1
    rw [← mul_assoc, (hM.commute hW).eq, mul_assoc, hleft, mul_one]
  have heq : (U - c • 1) * toeplitz n b = M * toeplitz n (X * a) := by
    calc
      (U - c • 1) * toeplitz n b = (M * Z) * toeplitz n b := by rw [hMZ]
      _ = M * (Z * toeplitz n b) := mul_assoc _ _ _
      _ = M * toeplitz n (X * a) := by rw [hlift]
  have hexpand : U * toeplitz n b - c • toeplitz n b =
      toeplitz n (X * a) - star c • (U * toeplitz n (X * a)) := by
    simpa only [M, schurM, sub_mul, Matrix.smul_mul, one_mul] using heq
  have hD : toeplitz n (schurDenominator c a b) =
      toeplitz n b + star c • toeplitz n (X * a) := by
    simp only [schurDenominator, mul_assoc, toeplitz_add, toeplitz_C_mul]
  have hA : toeplitz n (schurNumerator c a b) =
      c • toeplitz n b + toeplitz n (X * a) := by
    simp only [schurNumerator, toeplitz_add, toeplitz_C_mul]
  -- Expose only the local U and c abbreviations so hD and hA rewrite the same matrices.
  change U * toeplitz n (schurDenominator c a b) = toeplitz n (schurNumerator c a b)
  rw [hD, hA, mul_add, Matrix.mul_smul]
  calc
    U * toeplitz n b + star c • (U * toeplitz n (X * a)) =
        (U * toeplitz n b - c • toeplitz n b) +
          (c • toeplitz n b + star c • (U * toeplitz n (X * a))) := by abel
    _ = (toeplitz n (X * a) - star c • (U * toeplitz n (X * a))) +
          (c • toeplitz n b + star c • (U * toeplitz n (X * a))) := by rw [hexpand]
    _ = c • toeplitz n b + toeplitz n (X * a) := by abel

private theorem schur_step_matrix_pullback {n : ℕ} (U : Square n) (c : ℂ) (a b : Poly)
    (hinterp : U * toeplitz n (schurDenominator c a b) = toeplitz n (schurNumerator c a b)) :
    schurM U c * toeplitz n (schurDenominator c a b) =
      (((1 - ‖c‖ ^ 2 : ℝ) : ℂ)) • toeplitz n b := by
  calc
    schurM U c * toeplitz n (schurDenominator c a b) =
        toeplitz n (schurDenominator c a b) -
          star c • (U * toeplitz n (schurDenominator c a b)) := by
      simp only [schurM, sub_mul, Matrix.smul_mul, one_mul]
    _ = toeplitz n (schurDenominator c a b) - star c • toeplitz n (schurNumerator c a b) := by
      rw [hinterp]
    _ = toeplitz n (schurDenominator c a b - C (star c) * schurNumerator c a b) := by
      rw [toeplitz_sub, toeplitz_C_mul]
    _ = (((1 - ‖c‖ ^ 2 : ℝ) : ℂ)) • toeplitz n b := by
      rw [(schur_polynomial_identities c a b).1, toeplitz_C_mul]

private theorem schur_matrix_coefficient_action {n : ℕ} (U : Square n) (a b h : Poly)
    (hinterp : U * toeplitz n b = toeplitz n a) :
    euclideanLin U (coeffVector n (b * h)) = coeffVector n (a * h) := by
  calc
    euclideanLin U (coeffVector n (b * h)) =
        euclideanLin U (euclideanLin (toeplitz n b) (coeffVector n h)) := by
      rw [toeplitz_action, coeffVector_mul_truncate]
    _ = euclideanLin (U * toeplitz n b) (coeffVector n h) :=
      (euclideanLin_mul_apply _ _ _).symm
    _ = euclideanLin (toeplitz n a) (coeffVector n h) := by rw [hinterp]
    _ = coeffVector n (a * h) := by rw [toeplitz_action, coeffVector_mul_truncate]

theorem schur_pair_step {n d : ℕ} (p a b : Poly) (B : Square (n + 2))
    (hU : operatorNorm (toeplitz (n + 2) p) = 1) (hc : ‖p.coeff 0‖ < 1)
    (hleft : schurM (toeplitz (n + 2) p) (p.coeff 0) * B = 1)
    (hright : B * schurM (toeplitz (n + 2) p) (p.coeff 0) = 1)
    (hV : operatorNorm (activeBlock (schurZ (toeplitz (n + 2) p) (p.coeff 0) B)) = 1)
    (hpair : SchurPair (n + 1)
      (activeBlock (schurZ (toeplitz (n + 2) p) (p.coeff 0) B)) d a b) :
    SchurPair (n + 2) (toeplitz (n + 2) p) (d + 1)
      (schurNumerator (p.coeff 0) a b) (schurDenominator (p.coeff 0) a b) := by
  let U := toeplitz (n + 2) p
  let c := p.coeff 0
  let M := schurM U c
  let Z := schurZ U c B
  let V := activeBlock Z
  let A := schurNumerator c a b
  let D := schurDenominator c a b
  let α : ℂ := ((1 - ‖c‖ ^ 2 : ℝ) : ℂ)
  have hα : α ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (schur_alpha_pos c hc))
  obtain ⟨B0, _hB0, hleft0, _hright0, hZ0, hdiag0, hZnorm0,
    _hVnorm0, _henergy0, htransport0⟩ := schur_strict_reduction p hU hc
  have hBB0 : B = B0 := by
    calc
      B = B * (M * B0) := by rw [hleft0, mul_one]
      _ = (B * M) * B0 := (mul_assoc _ _ _).symm
      _ = B0 := by rw [hright, one_mul]
  subst B0
  have hZ : IsToeplitz Z := hZ0
  have hdiag : ∀ i, Z i i = 0 := hdiag0
  have hZnorm : operatorNorm Z = 1 := hZnorm0
  have htransport (x : H (n + 2)) :
      x ∈ maximalSpace U ↔ euclideanLin M x ∈ maximalSpace Z := htransport0 x
  have hBM (x : H (n + 2)) : euclideanLin B (euclideanLin M x) = x := by
    rw [← euclideanLin_mul_apply, hright, euclideanLin_one_apply]
  rcases hpair with ⟨hd, ha, hb, hb0, hab, hdisk, hcircle,
    holdinterp, holdmax, _holdaction, holdrank⟩
  have hdle : d ≤ n := by omega
  have hmold : n + 1 - 1 - d = n - d := by omega
  have hmnew : n + 2 - 1 - (d + 1) = n - d := by omega
  have holdmax' (g : H (n + 1)) : g ∈ maximalSpace V ↔
      ∃ h : Poly, DegreeLE h (n - d) ∧ g = coeffVector (n + 1) (b * h) := by
    simpa only [hmold] using holdmax g
  have hprod (h : Poly) (hh : DegreeLE h (n - d)) : DegreeLE (b * h) n := by
    have heq : d + (n - d) = n := Nat.add_sub_of_le hdle
    simpa only [heq] using schur_degree_mul_bound b h hb hh
  have hlift : Z * toeplitz (n + 2) b = toeplitz (n + 2) (X * a) :=
    schur_lift_interpolation Z a b hZ hdiag holdinterp
  have hinterp : U * toeplitz (n + 2) D = toeplitz (n + 2) A :=
    schur_step_matrix_interpolation p a b B hleft hlift
  have hpullmat : M * toeplitz (n + 2) D = α • toeplitz (n + 2) b :=
    schur_step_matrix_pullback U c a b hinterp
  have hpull (h : Poly) : euclideanLin M (coeffVector (n + 2) (D * h)) =
      α • coeffVector (n + 2) (b * h) := by
    calc
      euclideanLin M (coeffVector (n + 2) (D * h)) =
          euclideanLin M (euclideanLin (toeplitz (n + 2) D) (coeffVector (n + 2) h)) := by
        rw [toeplitz_action, coeffVector_mul_truncate]
      _ = euclideanLin (M * toeplitz (n + 2) D) (coeffVector (n + 2) h) :=
        (euclideanLin_mul_apply _ _ _).symm
      _ = euclideanLin (α • toeplitz (n + 2) b) (coeffVector (n + 2) h) := by rw [hpullmat]
      _ = α • coeffVector (n + 2) (b * h) := by
        rw [euclideanLin_smul_apply, toeplitz_action, coeffVector_mul_truncate]
  have hmax (x : H (n + 2)) : x ∈ maximalSpace U ↔
      ∃ h : Poly, DegreeLE h (n - d) ∧ x = coeffVector (n + 2) (D * h) := by
    constructor
    · intro hx
      have hy := (schur_maximal_prefix Z hZ hdiag hZnorm hV _).mp ((htransport x).mp hx)
      obtain ⟨h, hh, hg⟩ := (holdmax' _).mp hy.2
      have hMx : euclideanLin M x = coeffVector (n + 2) (b * h) := by
        rw [hy.1, hg, ← schur_coeffVector_append (b * h) (hprod h hh)]
      let h' := α⁻¹ • h
      have hh' : DegreeLE h' (n - d) := (Polynomial.degree_smul_le α⁻¹ h).trans hh
      have heq : euclideanLin M (coeffVector (n + 2) (D * h')) = euclideanLin M x := by
        rw [hpull, hMx]
        dsimp only [h']
        rw [mul_smul_comm, schur_coeffVector_smul, smul_smul, mul_inv_cancel₀ hα, one_smul]
      refine ⟨h', hh', ?_⟩
      have hcancel := congrArg (euclideanLin B) heq
      rw [hBM, hBM] at hcancel
      exact hcancel.symm
    · rintro ⟨h, hh, rfl⟩
      apply (htransport _).mpr
      rw [hpull]
      apply (maximalSpace Z).smul_mem
      rw [schur_coeffVector_append (b * h) (hprod h hh)]
      apply (schur_maximal_append Z hZ hdiag hZnorm hV _ 0).mpr
      exact ⟨rfl, (holdmax' _).mpr ⟨h, hh, rfl⟩⟩
  have hdim : Module.finrank ℂ (maximalSpace U) = (n + 2) - (d + 1) := by
    calc
      Module.finrank ℂ (maximalSpace U) = Module.finrank ℂ (maximalSpace V) :=
        schur_maximal_finrank U Z M B hleft hright hZ hdiag hZnorm hV htransport
      _ = (n + 1) - d := holdrank
      _ = (n + 2) - (d + 1) := by omega
  obtain ⟨hdegree, hDdegree, hDzero⟩ := schur_polynomial_degrees c a b ha hb hb0
  obtain ⟨hnewdisk, hnewcircle⟩ := schur_polynomial_disk_boundary c a b hc hdisk hcircle
  -- These are exactly the eleven clauses of the frozen SchurPair definition.
  change SchurPair (n + 2) U (d + 1) A D
  refine ⟨by omega, hdegree, hDdegree, hDzero,
    schur_polynomial_coprime c a b hc hb0 hab, hnewdisk, hnewcircle, hinterp, ?_, ?_, hdim⟩
  · intro x
    simpa only [hmnew] using hmax x
  · intro h _hh
    exact schur_matrix_coefficient_action U A D h hinterp

#print axioms schur_pair_step
#assert_trust kernel schur_pair_step

end
end NLA.IE02
