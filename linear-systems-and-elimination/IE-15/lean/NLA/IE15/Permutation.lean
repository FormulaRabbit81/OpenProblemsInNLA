/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

The original mathematical resolution is George Stepaniants's 11 September
2026 proof. This formalization uses substantial OpenAI Codex assistance.
-/
import NLA.IE15.Definitions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace NLA.IE15

/-- The product of the literal row (or column) interchanges from stage `k` onward. -/
def tailPerm {n : ℕ} (p : Fin n → Fin n) (k : ℕ) : Equiv.Perm (Fin n) :=
  if h : k < n then
    (tailPerm p (k + 1)).trans (Equiv.swap ⟨k, h⟩ (p ⟨k, h⟩))
  else Equiv.refl _
termination_by n - k

theorem tailPerm_step {n : ℕ} (p : Fin n → Fin n) (k : ℕ) (hk : k < n)
    (i : Fin n) :
    tailPerm p k i = Equiv.swap ⟨k, hk⟩ (p ⟨k, hk⟩) (tailPerm p (k+1) i) := by
  rw [tailPerm, dif_pos hk]
  rfl

/-- Future interchanges fix every index already eliminated. -/
theorem tailPerm_fix {n : ℕ} (p : Fin n → Fin n) (hp : ∀ i, i ≤ p i)
    (k : ℕ) (i : Fin n) (hi : i.val < k) : tailPerm p k i = i := by
  rw [tailPerm]
  split
  next hk =>
    change Equiv.swap ⟨k, hk⟩ (p ⟨k, hk⟩) (tailPerm p (k+1) i) = i
    rw [tailPerm_fix p hp (k+1) i (by omega)]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h
      have hpi := hp ⟨k, hk⟩
      have hiv : i.val = (p ⟨k, hk⟩).val := congrArg Fin.val h
      change k ≤ (p ⟨k, hk⟩).val at hpi
      omega
  next hk => rfl
termination_by n - k

/-- A permutation fixing earlier indices preserves the remaining active block. -/
theorem perm_active_iff {n : ℕ} (e : Equiv.Perm (Fin n)) (k : ℕ)
    (he : ∀ i : Fin n, i.val < k → e i = i) (i : Fin n) :
    k ≤ (e i).val ↔ k ≤ i.val := by
  constructor
  · intro h
    by_contra hi
    have hfix := he i (by omega)
    rw [hfix] at h
    omega
  · intro h
    by_contra hi
    have hfix := he (e i) (by omega)
    have hie : e i = i := e.injective hfix
    rw [hie] at hi
    omega

theorem tailPerm_active_iff {n : ℕ} (p : Fin n → Fin n) (hp : ∀ i, i ≤ p i)
    (k : ℕ) (i : Fin n) :
    k ≤ (tailPerm p k i).val ↔ k ≤ i.val :=
  perm_active_iff _ k (tailPerm_fix p hp k) i

/-- An active-block preserving reindexing preserves its finite maximum exactly. -/
theorem activeMax_reindex {n : ℕ} (S : Mat n) (k : ℕ)
    (e f : Equiv.Perm (Fin n))
    (he : ∀ i, k ≤ (e i).val ↔ k ≤ i.val)
    (hf : ∀ j, k ≤ (f j).val ↔ k ≤ j.val) :
    activeMax (fun i j => S (e i) (f j)) k = activeMax S k := by
  unfold activeMax activeMaxNN
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro ij _
    have h := Finset.le_sup (f := fun ab : Fin n × Fin n =>
      if k ≤ ab.1.val ∧ k ≤ ab.2.val then ‖S ab.1 ab.2‖₊ else 0)
      (Finset.mem_univ (e ij.1, f ij.2))
    simpa only [he, hf] using h
  · apply Finset.sup_le
    intro ij _
    have h := Finset.le_sup (f := fun ab : Fin n × Fin n =>
      if k ≤ ab.1.val ∧ k ≤ ab.2.val then ‖S (e ab.1) (f ab.2)‖₊ else 0)
      (Finset.mem_univ (e.symm ij.1, f.symm ij.2))
    have hei := he (e.symm ij.1)
    have hfj := hf (f.symm ij.2)
    simp only [Equiv.apply_symm_apply] at h hei hfj
    simpa only [← hei, ← hfj] using h

theorem entryMax_reindex {n : ℕ} (A : Mat n) (e f : Equiv.Perm (Fin n)) :
    entryMax (fun i j => A (e i) (f j)) = entryMax A := by
  have h := activeMax_reindex A 0 e f (by simp) (by simp)
  simpa [activeMax, activeMaxNN, entryMax, entryMaxNN] using h

/-- Schur complementation commutes with permutations of the strictly trailing block. -/
theorem schurStep_reindex {n : ℕ} (S : Mat n) (k r c : Fin n)
    (e f : Equiv.Perm (Fin n)) (hek : e k = k) (hfk : f k = k)
    (he : ∀ i, k < e i ↔ k < i) (hf : ∀ j, k < f j ↔ k < j) :
    schurStep (fun i j => S (Equiv.swap k r (e i)) (Equiv.swap k c (f j))) k k k =
      fun i j => schurStep S k r c (e i) (f j) := by
  funext i j
  simp only [schurStep, pivotSwap, Equiv.swap_self, Equiv.refl_apply, hek, hfk, he, hf]

/-- Globally move each selected pivot to the diagonal in its eventual elimination order. -/
def reorderForPath {n : ℕ} (A : Mat n) (path : PivotPath n) : Mat n :=
  fun i j => A (tailPerm (fun k => (path k).1) 0 i)
    (tailPerm (fun k => (path k).2) 0 j)

/-- At each stage, the two trajectories differ only by future interchanges. -/
theorem trajectory_reorderForPath {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hr : ∀ k, k ≤ (path k).1) (hc : ∀ k, k ≤ (path k).2)
    (k : ℕ) (hk : k ≤ n) :
    trajectory (reorderForPath A path) (noSwapPath n) k =
      fun i j => trajectory A path k (tailPerm (fun l => (path l).1) k i)
        (tailPerm (fun l => (path l).2) k j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hk' : k ≤ n := by omega
    simp only [trajectory, dif_pos hkn, noSwapPath]
    rw [ih hk']
    simp only [tailPerm_step (fun l => (path l).1) k hkn,
      tailPerm_step (fun l => (path l).2) k hkn]
    apply schurStep_reindex
    · exact tailPerm_fix _ hr (k+1) ⟨k, hkn⟩ (by simp)
    · exact tailPerm_fix _ hc (k+1) ⟨k, hkn⟩ (by simp)
    · intro i
      have h := tailPerm_active_iff (fun l => (path l).1) hr (k+1) i
      change k < (tailPerm (fun l => (path l).1) (k+1) i).val ↔ k < i.val
      omega
    · intro j
      have h := tailPerm_active_iff (fun l => (path l).2) hc (k+1) j
      change k < (tailPerm (fun l => (path l).2) (k+1) j).val ↔ k < j.val
      omega

theorem tailPerm_pivot {n : ℕ} (p : Fin n → Fin n) (hp : ∀ i, i ≤ p i)
    (k : Fin n) : tailPerm p k.val k = p k := by
  rw [tailPerm_step p k.val k.isLt, tailPerm_fix p hp (k.val+1) k (by omega)]
  simp

/-- All rook inequalities, including ties and pivot nonvanishing, are preserved. -/
theorem admissiblePath_reorderForPath {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) :
    AdmissiblePath (reorderForPath A path) (noSwapPath n) := by
  have hr : ∀ k, k ≤ (path k).1 := fun k => (hp k).1
  have hc : ∀ k, k ≤ (path k).2 := fun k => (hp k).2.1
  intro k
  change AdmissiblePivot (trajectory (reorderForPath A path) (noSwapPath n) k.val) k k k
  rw [trajectory_reorderForPath A path hr hc k.val (Nat.le_of_lt k.isLt)]
  rcases hp k with ⟨_, _, hnz, hrow, hcol⟩
  refine ⟨le_rfl, le_rfl, ?_, ?_, ?_⟩
  · simpa only [tailPerm_pivot (fun l => (path l).1) hr,
      tailPerm_pivot (fun l => (path l).2) hc] using hnz
  · intro j hj
    simp only [tailPerm_pivot (fun l => (path l).1) hr,
      tailPerm_pivot (fun l => (path l).2) hc]
    apply hrow
    exact (tailPerm_active_iff (fun l => (path l).2) hc k.val j).2 hj
  · intro i hi
    simp only [tailPerm_pivot (fun l => (path l).1) hr,
      tailPerm_pivot (fun l => (path l).2) hc]
    apply hcol
    exact (tailPerm_active_iff (fun l => (path l).1) hr k.val i).2 hi

theorem entryMax_reorderForPath {n : ℕ} (A : Mat n) (path : PivotPath n) :
    entryMax (reorderForPath A path) = entryMax A :=
  entryMax_reindex A _ _

theorem activeMax_reorderForPath {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : Fin n) :
    activeMax (trajectory (reorderForPath A path) (noSwapPath n) k.val) k.val =
      activeMax (trajectory A path k.val) k.val := by
  have hr : ∀ k, k ≤ (path k).1 := fun k => (hp k).1
  have hc : ∀ k, k ≤ (path k).2 := fun k => (hp k).2.1
  rw [trajectory_reorderForPath A path hr hc k.val (Nat.le_of_lt k.isLt)]
  exact activeMax_reindex _ _ _ _ (tailPerm_active_iff _ hr k.val)
    (tailPerm_active_iff _ hc k.val)

/-- Every admissible path has an exactly growth-equivalent input with diagonal pivots.
No nonsingularity assumption or determinant computation is required for this reduction. -/
theorem exists_noSwap_representative {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) :
    ∃ B : Mat n, entryMax B = entryMax A ∧ AdmissiblePath B (noSwapPath n) ∧
      ∀ k : Fin n, activeMax (trajectory B (noSwapPath n) k.val) k.val =
        activeMax (trajectory A path k.val) k.val := by
  exact ⟨reorderForPath A path, entryMax_reorderForPath A path,
    admissiblePath_reorderForPath A path hp, activeMax_reorderForPath A path hp⟩

end NLA.IE15
