/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Exact rank-one reconstruction from the
Schur tail and its actual row/column sums, following Colbrook's NM-04 proof.
-/
import NLA.NM04.SchurMargins
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix

theorem schur_rank_one_reconstruction {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (hS : Positive S) (hB : Balanced S) :
    tailMatrix S = schurTail S hm hn +
      S (firstIndex hm) (firstIndex hn) • Matrix.vecMulVec
        (fun i : Tail m => 1 - ∑ j : Tail n, schurTail S hm hn i j)
        (fun j : Tail n => 1 - ((n : ℝ) / (m : ℝ)) *
          ∑ i : Tail m, schurTail S hm hn i j) := by
  have hx := ne_of_gt (hS (firstIndex hm) (firstIndex hn))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  obtain ⟨hr, hc, _⟩ := schur_margin_identities hm hn S hS hB
  ext i j
  have hu : 1 - (∑ t : Tail n, schurTail S hm hn i t) =
      S i.val (firstIndex hn) / S (firstIndex hm) (firstIndex hn) := by
    rw [hr i]
    ring
  have hv : 1 - ((n : ℝ) / (m : ℝ)) * (∑ s : Tail m, schurTail S hm hn s j) =
      S (firstIndex hm) j.val / S (firstIndex hm) (firstIndex hn) := by
    rw [hc j]
    field_simp
    ring
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [hu, hv]
  simp only [tailMatrix, schurTail]
  field_simp
  ring

#print axioms schur_rank_one_reconstruction
#assert_trust kernel schur_rank_one_reconstruction

end
end NLA.NM04
