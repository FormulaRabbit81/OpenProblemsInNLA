/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.PairingVectors
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

/-- A double induction handles arbitrary Jordan chains without diagonalizability. -/
theorem generalized_stein_pairing {n : ℕ} (S H : Mat n) (lam μ : ℂ)
    (hstein : H = S.conjTranspose * H * S)
    (hnonres : 1 - star lam * μ ≠ 0) (k l : ℕ) (v w : Vec n)
    (hv : ((S - lam • (1 : Mat n)) ^ k).mulVec v = 0)
    (hw : ((S - μ • (1 : Mat n)) ^ l).mulVec w = 0) :
    pairing H v w = 0 := by
  induction k generalizing l v w with
  | zero =>
    have hv0 : v = 0 := by simpa only [pow_zero, Matrix.one_mulVec] using hv
    rw [hv0, pairing_zero_left]
  | succ k ihk =>
    induction l generalizing w with
    | zero =>
      have hw0 : w = 0 := by simpa only [pow_zero, Matrix.one_mulVec] using hw
      rw [hw0, pairing_zero_right]
    | succ l ihl =>
      let v' := (S - lam • (1 : Mat n)).mulVec v
      let w' := (S - μ • (1 : Mat n)).mulVec w
      have hv' : ((S - lam • (1 : Mat n)) ^ k).mulVec v' = 0 := by
        dsimp only [v']
        rw [Matrix.mulVec_mulVec, ← pow_succ]
        exact hv
      have hw' : ((S - μ • (1 : Mat n)) ^ l).mulVec w' = 0 := by
        dsimp only [w']
        rw [Matrix.mulVec_mulVec, ← pow_succ]
        exact hw
      have h₁ : pairing H v' w = 0 := ihk (l + 1) v' w hv' hw
      have h₂ : pairing H v w' = 0 := ihl w' hw'
      have h₃ : pairing H v' w' = 0 := ihk l v' w' hv' hw'
      have hSv : S.mulVec v = lam • v + v' := by
        dsimp only [v']
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        abel
      have hSw : S.mulVec w = μ • w + w' := by
        dsimp only [w']
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        abel
      have he := congrArg (fun M : Mat n => pairing M v w) hstein
      rw [pairing_conjugate_transform, hSv, hSw] at he
      simp only [pairing_add_left, pairing_add_right, pairing_smul_left,
        pairing_smul_right, h₁, h₂, h₃, mul_zero, add_zero] at he
      have hmul : (1 - star lam * μ) * pairing H v w = 0 := by
        calc
          _ = pairing H v w - μ * (star lam * pairing H v w) := by ring
          _ = 0 := sub_eq_zero.mpr he
      exact (mul_eq_zero.mp hmul).resolve_left hnonres

#print axioms generalized_stein_pairing

end NLA.MF18
