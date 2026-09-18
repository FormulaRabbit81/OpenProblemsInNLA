/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.

Finite support and an actual nonzero extreme Fourier coefficient. Positivity
comes from a coefficient of one of the supplied polynomials, not a factor oracle.
-/
import NLA.IE02.FourierSemantics
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem sumSquares_pos {l : ℕ} (q : Fin l → Poly) (z : ℂ)
    (h : ∃ j, (q j).eval z ≠ 0) : 0 < sumSquares q z := by
  obtain ⟨j, hj⟩ := h
  apply Finset.sum_pos' (fun i _hi => sq_nonneg ‖(q i).eval z‖)
  exact ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem fourier_outside_band {l : ℕ} (m : ℕ) (q : Fin l → Poly) (r : ℤ)
    (hr : r < -(m : ℤ) ∨ (m : ℤ) < r) : fourierCoeff m q r = 0 := by
  classical
  unfold fourierCoeff
  apply Finset.sum_eq_zero
  intro j _hj
  apply Finset.sum_eq_zero
  intro u _hu
  apply Finset.sum_eq_zero
  intro v _hv
  have hne : (u.val : ℤ) - (v.val : ℤ) ≠ r := by omega
  simp only [if_neg hne]

theorem fourier_zero_ne_zero {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m)
    (hno : ∀ z : ℂ, ‖z‖ = 1 → ∃ j, (q j).eval z ≠ 0) :
    fourierCoeff m q 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := hno 1 (norm_one : ‖(1 : ℂ)‖ = 1)
  have hp : q j ≠ 0 := by
    intro hz
    apply hj
    simp only [hz, Polynomial.eval_zero]
  have hc : (q j).coeff (q j).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  let i : Fin (m + 1) := ⟨(q j).natDegree,
    Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le (hq j))⟩
  rw [fourier_zero_coefficient]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Finset.sum_pos'
    (fun a _ha => Finset.sum_nonneg (fun b _hb => sq_nonneg ‖(q a).coeff b.val‖))
  refine ⟨j, Finset.mem_univ j, ?_⟩
  apply Finset.sum_pos' (fun b _hb => sq_nonneg ‖(q j).coeff b.val‖)
  exact ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hc) 2⟩

theorem fourier_effective_band {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hc0 : fourierCoeff m q 0 ≠ 0) :
    ∃ ell : ℕ, ell ≤ m ∧ fourierCoeff m q (ell : ℤ) ≠ 0 ∧
      ∀ r : ℤ, r < -(ell : ℤ) ∨ (ell : ℤ) < r → fourierCoeff m q r = 0 := by
  classical
  let s : Finset ℕ := (Finset.range (m + 1)).filter (fun k : ℕ => fourierCoeff m q (k : ℤ) ≠ 0)
  have hzero : 0 ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hc0⟩
  have hs : s.Nonempty := ⟨0, hzero⟩
  let ell : ℕ := s.max' hs
  have hell : ell ∈ s := s.max'_mem hs
  obtain ⟨hbound, hcell⟩ := Finset.mem_filter.mp hell
  have hle : ell ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hbound)
  have hupper (r : ℤ) (hr : (ell : ℤ) < r) : fourierCoeff m q r = 0 := by
    by_cases hmr : (m : ℤ) < r
    · exact fourier_outside_band m q r (Or.inr hmr)
    · have hr0 : 0 ≤ r := by omega
      have hcast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
      by_contra hc
      have hk : r.toNat ∈ s := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        simpa only [hcast] using hc
      have hmax : r.toNat ≤ ell := s.le_max' r.toNat hk
      omega
  refine ⟨ell, hle, hcell, ?_⟩
  intro r hr
  rcases hr with hr | hr
  · have hneg := hupper (-r) (by omega)
    have hstar := congrArg star (fourier_conjugate_symmetry m q r)
    rw [hneg, star_zero, star_star] at hstar
    exact hstar.symm
  · exact hupper r hr

#print axioms sumSquares_pos
#assert_trust kernel sumSquares_pos
#print axioms fourier_outside_band
#assert_trust kernel fourier_outside_band
#print axioms fourier_zero_ne_zero
#assert_trust kernel fourier_zero_ne_zero
#print axioms fourier_effective_band
#assert_trust kernel fourier_effective_band

end
end NLA.IE02
