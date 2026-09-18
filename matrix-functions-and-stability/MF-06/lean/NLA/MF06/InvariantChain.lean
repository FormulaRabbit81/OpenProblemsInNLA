/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The common-invariant chain is constructed from well-founded submodule orders.
Saturation is among actual common invariant subspaces, not all subspaces.
Strict finrank growth bounds the number of nonzero quotient blocks by d.
The later adapted-basis and quotient arguments are separate obligations.
-/
import NLA.MF06.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Order.OrderIsoNat

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma familyInvariant_bot {d : ℕ} (M : Set (Square d)) : FamilyInvariant M ⊥ := by
  intro A _ x hx
  change x = 0 at hx
  subst x
  simp [applyMatrix]

lemma familyInvariant_top {d : ℕ} (M : Set (Square d)) : FamilyInvariant M ⊤ := by
  intro A _ x _
  exact Submodule.mem_top

/-- No nontrivial common invariant subspace can be inserted into this finite
chain. The family itself need not be compact, nonempty, or finite. -/
lemma exists_saturated_invariant_chain {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d)) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ d ∧
      ∃ F : Fin (r + 1) → Submodule ℂ (EuclideanVector d),
        F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧ StrictMono F ∧
        (∀ i, FamilyInvariant M (F i)) ∧
        ∀ i : Fin r, ∀ T : Submodule ℂ (EuclideanVector d), FamilyInvariant M T →
          F i.castSucc ≤ T → T ≤ F i.succ → T = F i.castSucc ∨ T = F i.succ := by
  let I := {S : Submodule ℂ (EuclideanVector d) // FamilyInvariant M S}
  let bottom : I := ⟨⊥, familyInvariant_bot M⟩
  let top : I := ⟨⊤, familyInvariant_top M⟩
  obtain ⟨s, hs0, r, hsr, hcov⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (show bottom ≤ top from by
      change (⊥ : Submodule ℂ (EuclideanVector d)) ≤ ⊤
      exact bot_le)
  have hzero : (s 0).val = ⊥ := congrArg Subtype.val hs0
  have hlast : (s r).val = ⊤ := congrArg Subtype.val hsr
  have hr : r ≠ 0 := by
    intro hz
    subst r
    have hbad := congrArg (fun S : Submodule ℂ (EuclideanVector d) => Module.finrank ℂ S)
      (hzero.symm.trans hlast)
    simp only [finrank_bot, finrank_top, finrank_euclideanSpace_fin] at hbad
    omega
  have hdim : ∀ i : ℕ, i ≤ r → i ≤ Module.finrank ℂ (s i).val := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
        intro hi
        exact (Nat.succ_le_succ (ih (by omega))).trans
          (Nat.succ_le_of_lt (Submodule.finrank_strictMono (hcov i (by omega)).lt))
  have hrle : r ≤ d := by
    calc
      r ≤ Module.finrank ℂ (s r).val := hdim r le_rfl
      _ = Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanVector d)) :=
        congrArg (fun S : Submodule ℂ (EuclideanVector d) => Module.finrank ℂ S) hlast
      _ = d := by simp only [finrank_top, finrank_euclideanSpace_fin]
  refine ⟨r, Nat.one_le_iff_ne_zero.mpr hr, hrle, fun i => (s i.val).val,
    hzero, hlast, ?_, (fun i => (s i.val).property), ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact (hcov i.val i.isLt).lt
  · intro i T hT hleft hright
    rcases (hcov i.val i.isLt).eq_or_eq (c := (⟨T, hT⟩ : I)) hleft hright with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

#print axioms exists_saturated_invariant_chain
#assert_trust kernel exists_saturated_invariant_chain

end NLA.MF06
