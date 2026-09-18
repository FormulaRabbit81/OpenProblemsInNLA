/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Exact finite root enumeration retains all algebraic multiplicities. These
foundations support the later compactness proof of the half-plane count.
They do not assume continuous root labels or simple roots.
-/
import NLA.MF18.Definitions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.Polynomial.CauchyBound

set_option autoImplicit false
open scoped BigOperators NNReal

noncomputable section
namespace NLA.MF18

theorem exists_fin_multiset_enumeration {α : Type*} (s : Multiset α) (N : ℕ)
    (hc : s.card = N) : ∃ r : Fin N → α, Finset.univ.val.map r = s := by
  classical
  have hlen : s.toList.length = N := (Multiset.length_toList s).trans hc
  rw [← hlen]
  exact ⟨s.toList.get, by simp only [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

theorem exists_roots_enumeration (p : CPoly) (N : ℕ) (hd : p.natDegree = N) :
    ∃ r : Fin N → ℂ, Finset.univ.val.map r = p.roots :=
  exists_fin_multiset_enumeration p.roots N (IsAlgClosed.card_roots_eq_natDegree.trans hd)

theorem monic_eq_prod_root_enumeration {N : ℕ} (p : CPoly) (hp : p.Monic)
    (r : Fin N → ℂ) (hr : Finset.univ.val.map r = p.roots) :
    p = ∏ i : Fin N, (Polynomial.X - Polynomial.C (r i)) := by
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp, ← hr, Multiset.map_map]
  rfl

theorem isRoot_of_root_enumeration {N : ℕ} (p : CPoly) (r : Fin N → ℂ)
    (hr : Finset.univ.val.map r = p.roots) (i : Fin N) : p.IsRoot (r i) := by
  apply Polynomial.isRoot_of_mem_roots
  rw [← hr]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

theorem halfPlane_count_root_enumeration {N : ℕ} (p : CPoly) (r : Fin N → ℂ)
    (hr : Finset.univ.val.map r = p.roots) :
    rightHalfPlaneRootCount p = (Finset.univ.filter (fun i : Fin N => 0 < (r i).re)).card := by
  classical
  unfold rightHalfPlaneRootCount
  rw [← hr, Multiset.filter_map, Multiset.card_map]
  rfl

theorem monic_root_norm_bound (p : CPoly) (hp : p.Monic) (M : ℝ≥0)
    (hc : ∀ j < p.natDegree, ‖p.coeff j‖₊ ≤ M) (z : ℂ) (hz : p.IsRoot z) :
    ‖z‖₊ < M + 1 := by
  apply (hz.norm_lt_cauchyBound hp.ne_zero).trans_le
  unfold Polynomial.cauchyBound
  rw [hp.leadingCoeff, nnnorm_one, div_one]
  exact add_le_add (Finset.sup_le fun j hj => hc j (Finset.mem_range.mp hj)) (le_refl 1)

#print axioms exists_roots_enumeration
#print axioms monic_eq_prod_root_enumeration
#print axioms halfPlane_count_root_enumeration
#print axioms monic_root_norm_bound

end NLA.MF18
