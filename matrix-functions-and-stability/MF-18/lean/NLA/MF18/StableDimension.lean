/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Generalized eigenspaces, not ordinary eigenspaces, retain the full interior
Jordan multiplicities. Finite support is extracted from the root multiset.
-/
import NLA.MF18.Definitions
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem independent_finset_sup_finrank {K : Type*} {V : Type*} {ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : ι → Submodule K V) (hW : iSupIndep W) (s : Finset ι) :
    Module.finrank K (s.sup W : Submodule K V) = ∑ i ∈ s, Module.finrank K (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd : Disjoint (W i) (s.sup W) := by
      simpa only [Finset.sup_eq_iSup, Finset.mem_coe] using
        (hW.disjoint_biSup (y := (s : Set ι)) hi)
    have he := Submodule.finrank_sup_add_finrank_inf_eq (W i) (s.sup W)
    rw [hd.eq_bot, finrank_bot, add_zero] at he
    rw [Finset.sup_insert, Finset.sum_insert hi, he, ih]

theorem maxGenEigenspace_eq_bot_of_not_root {n : ℕ} (S : Mat n) (lam : ℂ)
    (hroot : lam ∉ S.charpoly.roots) : (Module.End.maxGenEigenspace S.toLin') lam = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin',
    ← Polynomial.count_roots]
  exact Multiset.count_eq_zero.mpr hroot

theorem stable_space_dimension {n : ℕ} (S : Mat n) :
    Module.finrank ℂ (stableSubspace S) = diskRootCount S.charpoly := by
  classical
  let s := (S.charpoly.roots.filter (fun lam : ℂ => ‖lam‖ < 1)).toFinset
  have hs : stableSubspace S = s.sup (Module.End.maxGenEigenspace S.toLin') := by
    rw [Finset.sup_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      intro lam
      apply iSup_le
      intro hlam
      by_cases hr : lam ∈ S.charpoly.roots
      · exact le_iSup_of_le lam (le_iSup_of_le
          (Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hr, hlam⟩)) le_rfl)
      · rw [maxGenEigenspace_eq_bot_of_not_root S lam hr]
        exact bot_le
    · apply iSup_le
      intro lam
      apply iSup_le
      intro hlam
      have hn : ‖lam‖ < 1 := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hlam)).2
      exact le_iSup_of_le lam (le_iSup_of_le hn le_rfl)
  calc
    Module.finrank ℂ (stableSubspace S) =
        ∑ lam ∈ s, Module.finrank ℂ ((Module.End.maxGenEigenspace S.toLin') lam) := by
      rw [hs]
      exact independent_finset_sup_finrank _ (Module.End.independent_maxGenEigenspace S.toLin') s
    _ = ∑ lam ∈ s, (S.charpoly.roots.filter (fun z : ℂ => ‖z‖ < 1)).count lam := by
      apply Finset.sum_congr rfl
      intro lam hlam
      have hn : ‖lam‖ < 1 := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hlam)).2
      rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin',
        Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ < 1) (a := lam) hn, Polynomial.count_roots]
    _ = diskRootCount S.charpoly := Multiset.toFinset_sum_count_eq _

#print axioms stable_space_dimension

end NLA.MF18
