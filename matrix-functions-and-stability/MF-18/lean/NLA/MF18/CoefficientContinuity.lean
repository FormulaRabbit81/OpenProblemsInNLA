/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Coefficient continuity is proved by finite algebraic sums and products;
no topology on the unbounded polynomial ring is assumed.
-/
import NLA.MF18.Definitions
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem coeffContinuousOn_const (s : Set ℝ) (p : CPoly) :
    CoeffContinuousOn (fun _ => p) s := fun _ => continuousOn_const

theorem coeffContinuousOn_C {s : Set ℝ} (f : ℝ → ℂ) (hf : ContinuousOn f s) :
    CoeffContinuousOn (fun t => Polynomial.C (f t)) s := by
  intro j
  by_cases hj : j = 0
  · simpa only [hj, Polynomial.coeff_C_zero] using hf
  · simpa only [Polynomial.coeff_C, if_neg hj] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) s)

theorem coeffContinuousOn_add {s : Set ℝ} (p q : ℝ → CPoly)
    (hp : CoeffContinuousOn p s) (hq : CoeffContinuousOn q s) :
    CoeffContinuousOn (fun t => p t + q t) s := by
  intro j
  simpa only [Polynomial.coeff_add, Pi.add_def] using (hp j).add (hq j)

theorem coeffContinuousOn_sub {s : Set ℝ} (p q : ℝ → CPoly)
    (hp : CoeffContinuousOn p s) (hq : CoeffContinuousOn q s) :
    CoeffContinuousOn (fun t => p t - q t) s := by
  intro j
  simpa only [Polynomial.coeff_sub, Pi.sub_def] using (hp j).sub (hq j)

theorem coeffContinuousOn_neg {s : Set ℝ} (p : ℝ → CPoly)
    (hp : CoeffContinuousOn p s) : CoeffContinuousOn (fun t => -(p t)) s := by
  intro j
  simpa only [Polynomial.coeff_neg, Pi.neg_def] using (hp j).neg

theorem coeffContinuousOn_mul {s : Set ℝ} (p q : ℝ → CPoly)
    (hp : CoeffContinuousOn p s) (hq : CoeffContinuousOn q s) :
    CoeffContinuousOn (fun t => p t * q t) s := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact continuousOn_finsetSum _ fun ij _ => (hp ij.1).mul (hq ij.2)

theorem coeffContinuousOn_sum {ι : Type*} {s : Set ℝ} (S : Finset ι) (p : ι → ℝ → CPoly)
    (hp : ∀ i ∈ S, CoeffContinuousOn (p i) s) :
    CoeffContinuousOn (fun t => ∑ i ∈ S, p i t) s := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  exact continuousOn_finsetSum S fun i hi => hp i hi j

theorem coeffContinuousOn_prod {ι : Type*} {s : Set ℝ} (S : Finset ι) (p : ι → ℝ → CPoly)
    (hp : ∀ i ∈ S, CoeffContinuousOn (p i) s) :
    CoeffContinuousOn (fun t => ∏ i ∈ S, p i t) s := by
  classical
  revert hp
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.prod_empty] using coeffContinuousOn_const s (1 : CPoly)
  | @insert i S hi ih =>
    intro hp
    simp only [Finset.prod_insert hi]
    exact coeffContinuousOn_mul _ _ (hp i (Finset.mem_insert_self i S))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem matrixDet_coeffContinuousOn {n : ℕ} {s : Set ℝ}
    (M : ℝ → Matrix (Fin n) (Fin n) CPoly)
    (hM : ∀ i j, CoeffContinuousOn (fun t => M t i j) s) :
    CoeffContinuousOn (fun t => (M t).det) s := by
  classical
  simp only [Matrix.det_apply]
  apply coeffContinuousOn_sum
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp only [hs, one_smul]
    exact coeffContinuousOn_prod _ _ fun i _ => hM (σ i) i
  · simp only [hs, Units.neg_smul, one_smul]
    exact coeffContinuousOn_neg _ (coeffContinuousOn_prod _ _ fun i _ => hM (σ i) i)

#print axioms matrixDet_coeffContinuousOn

end NLA.MF18
