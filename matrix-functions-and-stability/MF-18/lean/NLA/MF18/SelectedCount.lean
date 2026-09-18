/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The selected spectral count is deduced from the exact limiting factorization,
reciprocal symmetry, and both weak stability conclusions. Simplicity is
inherited only at actual unit roots; interior Jordan structure is unrestricted.
-/
import NLA.MF18.ReciprocalCount
import NLA.MF18.WeakComplement
import NLA.MF18.LimitingEquation
import NLA.MF18.UnregularizedFactorization
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem weakStable_disk_circle_count {n : ℕ} (S : Mat n) (hweak : WeakStable S) :
    diskRootCount S.charpoly + circleRootCount S.charpoly = n := by
  classical
  have hout : S.charpoly.roots.filter (fun z : ℂ => 1 < ‖z‖) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro z hz
    exact not_lt_of_ge (hweak z (Polynomial.isRoot_of_mem_roots hz))
  have hpart := norm_partition_card S.charpoly.roots
  rw [hout, Multiset.card_zero, add_zero, IsAlgClosed.card_roots_eq_natDegree,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hpart
  exact hpart

theorem simpleCircleRoots_factor (a : ℂ) (q s : CPoly)
    (ha : a ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (hsimple : SimpleCircleRoots (Polynomial.C a * (q * s))) : SimpleCircleRoots s := by
  intro lam hlam hroot
  -- IsRoot is the evaluation-zero predicate; expose its equality explicitly
  -- so the evaluator simplification can use it without unfolding all roots.
  have heval : s.eval lam = 0 := hroot
  have hp : (Polynomial.C a * (q * s)).IsRoot lam := by
    change (Polynomial.C a * (q * s)).eval lam = 0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, heval, mul_zero]
  have hm := hsimple lam hlam hp
  have hC : Polynomial.C a ≠ 0 := Polynomial.C_ne_zero.mpr ha
  have hqs : q * s ≠ 0 := mul_ne_zero hq hs
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hC hqs),
    Polynomial.rootMultiplicity_C, Polynomial.rootMultiplicity_mul hqs, zero_add] at hm
  have hpos : 0 < s.rootMultiplicity lam := (Polynomial.rootMultiplicity_pos hs).mpr hroot
  omega

theorem selected_spectrum_count {n : ℕ} [NeZero n] (C D R P : Mat n)
    (X : ℝ → Mat n) (X₀ : Mat n) (m : ℕ)
    (h : GreenAssumptions C D R P X X₀)
    (hcount : circleRootCount (unregularizedPolynomial C R) = 2 * m) :
    diskRootCount (X₀⁻¹ * C).charpoly + m = n ∧
    circleRootCount (X₀⁻¹ * C).charpoly = m ∧
    SimpleCircleRoots (X₀⁻¹ * C).charpoly := by
  have hlim := limiting_equation_and_spectra C D R P X X₀ h
  rcases h with ⟨hR, _hP, _hpos, _hstab, _hXlim, hXdet, hreg, hsimple⟩
  have hfactor := unregularized_polynomial_factorization C R X₀ hXdet hlim.1
  have hq := complementary_ne_zero C.conjTranspose X₀
  have hS := (Matrix.charpoly_monic (X₀⁻¹ * C)).ne_zero
  have hqcount := weak_complementary_disk_count C.conjTranspose X₀ hlim.2.2
  have hdisk : diskRootCount (unregularizedPolynomial C R) =
      diskRootCount (X₀⁻¹ * C).charpoly := by
    rw [hfactor, diskRootCount_C_mul X₀.det hXdet,
      diskRootCount_mul _ _ (mul_ne_zero hq hS), hqcount, zero_add]
  have hrec := (reciprocal_count_identity C R hR hreg).2
  rw [hdisk, hcount] at hrec
  have hdim := weakStable_disk_circle_count (X₀⁻¹ * C) hlim.2.1
  refine ⟨by omega, by omega, ?_⟩
  rw [hfactor] at hsimple
  exact simpleCircleRoots_factor X₀.det (complementaryPolynomial C.conjTranspose X₀)
    (X₀⁻¹ * C).charpoly hXdet hq hS hsimple

#print axioms selected_spectrum_count

end NLA.MF18
