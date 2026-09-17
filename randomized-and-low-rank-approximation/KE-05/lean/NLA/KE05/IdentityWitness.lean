import NLA.KE05.Recurrence

/- The commuting identity sample witnesses nonsingularity for every admissible
input and every root ordering. Repeated within-block eigenvalues are permitted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.KE05

 def identitySample (b d : ℕ) : Sample b d := fun ij => if ij.2.1 = ij.2.2 then 1 else 0

lemma omega_identity {b d : ℕ} (i : Fin d) : omega (identitySample b d) i = (1 : Mat b) := rfl

lemma baseBlock_identity {b d : ℕ} (L : Data b d) (k i : Fin d) :
    baseBlock L (identitySample b d) k i = Matrix.diagonal (L (rootOrder k i)) := by
  simp [baseBlock, omega_identity]

lemma rootOrder_injective {d : ℕ} (k : Fin d) : Function.Injective (rootOrder k) := by
  apply List.nodup_ofFn.mp
  rw [List.ofFn_eq_map, rootOrder_list]
  exact (List.perm_cons_erase (List.mem_finRange k)).nodup_iff.mp (List.nodup_finRange d)

lemma diagonal_similar {b : ℕ} (v l : Fin b → ℝ) (hv : ∀ r, v r ≠ 0) :
    (Matrix.diagonal v)⁻¹ * Matrix.diagonal l * Matrix.diagonal v = Matrix.diagonal l := by
  rw [Matrix.inv_diagonal]
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  have hu : IsUnit v := Pi.isUnit_iff.mpr (fun r => (hv r).isUnit)
  have hh := congrFun (Ring.inverse_mul_cancel v hu) r
  dsimp only [Pi.mul_apply, Pi.one_apply] at hh
  calc
    _ = (Ring.inverse v r * v r) * l r := by ring
    _ = l r := by rw [hh, one_mul]

lemma diagonal_nonzero_det {b : ℕ} (v : Fin b → ℝ) (hv : ∀ r, v r ≠ 0) :
    (Matrix.diagonal v).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun r _ => hv r)

lemma diagonal_difference_step {b : ℕ} (l m v : Fin b → ℝ) :
    Matrix.diagonal l * Matrix.diagonal v - Matrix.diagonal v * Matrix.diagonal m =
      Matrix.diagonal (fun r => v r * (l r - m r)) := by
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
  congr 1
  funext r
  try simp only [Pi.sub_apply, Pi.mul_apply]
  ring

lemma prefixS_identity_diagonal {b d : ℕ} (L : Data b d) (hL : Admissible L)
    (k i : Fin d) (hats : Fin d → Mat b)
    (hh : ∀ t, hats t = Matrix.diagonal (L (rootOrder k t))) (j : ℕ) :
    ∃ v : Fin b → ℝ, prefixS L (identitySample b d) k i hats j = Matrix.diagonal v ∧
      ∀ r, v r ≠ 0 := by
  let xs := (((List.finRange d).drop (i.val+1)).take (j-i.val))
  have hg : ∀ t ∈ xs, i ≠ t := by
    intro t ht
    exact ne_of_lt (prefix_index_gt i t j ht)
  have hf : ∀ (ys : List (Fin d)), (∀ t ∈ ys, i ≠ t) →
      ∀ v : Fin b → ℝ, (∀ r, v r ≠ 0) →
      ∃ v' : Fin b → ℝ,
        ys.foldl (fun S t => Matrix.diagonal (L (rootOrder k i)) * S - S * hats t)
          (Matrix.diagonal v) = Matrix.diagonal v' ∧ ∀ r, v' r ≠ 0 := by
    intro ys
    induction ys with
    | nil => intro _ v hv; exact ⟨v,rfl,hv⟩
    | cons t ys ih =>
      intro hy v hv
      simp only [List.foldl_cons, hh t, diagonal_difference_step]
      apply ih (fun z hz => hy z (by simp [hz]))
      intro r
      apply mul_ne_zero (hv r)
      exact sub_ne_zero.mpr (hL _ _ (fun he => hy t (by simp) ((rootOrder_injective k) he)) r r)
  have hhf := hf xs hg (fun _ => 1) (by simp)
  simpa only [prefixS, baseBlock_identity, Matrix.diagonal_one] using hhf

end NLA.KE05
