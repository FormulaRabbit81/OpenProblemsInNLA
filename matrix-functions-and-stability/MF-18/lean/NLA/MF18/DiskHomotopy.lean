/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.CayleyCount
import NLA.MF18.HalfPlaneHomotopy
import NLA.MF18.CoefficientContinuity

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem monicCayley_coeffContinuousOn (N : ℕ) (p : ℝ → CPoly) (s : Set ℝ)
    (hc : CoeffContinuousOn p s) (hd : ∀ t ∈ s, (p t).natDegree ≤ N)
    (h1 : ∀ t ∈ s, (p t).eval 1 ≠ 0) :
    CoeffContinuousOn (fun t => monicCayleyPolynomial N (p t)) s := by
  have heval : ContinuousOn (fun t => (p t).eval 1) s := by
    apply (continuousOn_finsetSum (Finset.range (N + 1)) (fun j _ => hc j)).congr
    intro t ht
    simpa only [one_pow, mul_one] using
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hd t ht)) (1 : ℂ)
  unfold monicCayleyPolynomial
  apply coeffContinuousOn_mul
  · exact coeffContinuousOn_C _ (heval.inv₀ h1)
  · unfold cayleyPolynomial
    apply coeffContinuousOn_sum
    intro j _
    exact coeffContinuousOn_mul _ _
      (coeffContinuousOn_mul _ _ (coeffContinuousOn_C _ (hc j))
        (coeffContinuousOn_const s ((Polynomial.X - 1) ^ j)))
      (coeffContinuousOn_const s ((Polynomial.X + 1) ^ (N - j)))

theorem bounded_degree_disk_count_homotopy (N : ℕ) (p : ℝ → CPoly)
    (hc : CoeffContinuousOn p (Set.Icc 0 1))
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p t).natDegree ≤ N)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℂ, ‖lam‖ = 1 → (p t).eval lam ≠ 0) :
    diskRootCount (p 0) = diskRootCount (p 1) := by
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p t).eval 1 ≠ 0 := fun t ht => hb t ht 1 (by simp)
  have hcount := monic_half_plane_count_homotopy N
    (fun t => monicCayleyPolynomial N (p t))
    (monicCayley_coeffContinuousOn N p (Set.Icc 0 1) hc hd h1)
    (fun t ht => monicCayley_monic_and_degree N (p t) (hd t ht) (h1 t ht))
    (fun t ht => cayley_boundary_transfer N (p t) (hd t ht) (hb t ht))
  rw [(cayley_degree_and_count N (p 0) (hd 0 (by simp)) (h1 0 (by simp))).2.2,
    (cayley_degree_and_count N (p 1) (hd 1 (by simp)) (h1 1 (by simp))).2.2]
  exact hcount

#print axioms monicCayley_coeffContinuousOn
#print axioms bounded_degree_disk_count_homotopy

end NLA.MF18
