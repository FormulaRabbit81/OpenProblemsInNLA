/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Colbrook's balanced-minor relation from
the actual Schur-tail margins and the universal polynomial minor identities.
The column, row and raising identities preserve singular and empty minors.
-/
import NLA.NM04.SchurReconstruction
import NLA.NM04.SchurBordered
import NLA.NM04.RankOneBordered
import NLA.NM04.CofactorDirections
import NLA.NM04.MinorLowering
import NLA.NM04.MinorColumnExchange
import NLA.NM04.MinorRowExchange
import NLA.NM04.MinorRaising
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
-- Match the frozen operator definitions and the generic minor-identity instances.
attribute [local instance] Classical.propDecidable

theorem balanced_minor_relation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (hS : Positive S) (hB : Balanced S) (I : Index m n) :
    (m : ℝ) * minor (tailMatrix S) I +
      ((I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) - (m : ℝ) * (n : ℝ)) * delta S hm hn I +
      (n : ℝ) * raising (delta S hm hn) I - (m : ℝ) * lowering (delta S hm hn) I +
      (m : ℝ) * columnExchange (delta S hm hn) I +
      (n : ℝ) * rowExchange (delta S hm hn) I = 0 := by
  let T : Matrix (Tail m) (Tail n) ℝ := schurTail S hm hn
  let x := S (firstIndex hm) (firstIndex hn)
  let b : ℝ := (n : ℝ) / (m : ℝ)
  have hx : x ≠ 0 := ne_of_gt (hS (firstIndex hm) (firstIndex hn))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have htotal : (∑ i : Tail m, ∑ j : Tail n, T i j) =
      (m : ℝ) - ((m : ℝ) / (n : ℝ)) / x :=
    (schur_margin_identities hm hn S hS hB).2.2
  have hdelta : delta S hm hn = fun J => x * minor T J :=
    funext (fun J => schur_bordered_minor hm hn S hx J)
  -- The generic identities use classical equality decisions. Transport only
  -- those decisions to the concrete Tail instances, retaining the enumerations.
  have hcolumn : cofactorForm T I (Matrix.vecMulVec (fun i => ∑ j, T i j) (fun _ => 1)) =
      (I.1.1.card : ℝ) * minor T I + columnExchange (minor T) I := by
    exact (minor_column_exchange_identity T I).trans
      (congrArg (fun d : DecidableEq (Tail m) =>
        (I.1.1.card : ℝ) * minor T I +
          @columnExchange (Tail m) (Tail n) ℝ _ _ d _ _ (minor T) I)
        (Subsingleton.elim _ _))
  have hrow : cofactorForm T I (Matrix.vecMulVec (fun _ => 1) (fun j => ∑ i, T i j)) =
      (I.1.1.card : ℝ) * minor T I + rowExchange (minor T) I := by
    exact (minor_row_exchange_identity T I).trans
      (congrArg (fun d : DecidableEq (Tail n) =>
        (I.1.1.card : ℝ) * minor T I +
          @rowExchange (Tail m) (Tail n) ℝ _ _ _ d _ (minor T) I)
        (Subsingleton.elim _ _))
  have hminor : minor (tailMatrix S) I = minor T I + x *
      (lowering (minor T) I -
        ((I.1.1.card : ℝ) * minor T I + columnExchange (minor T) I) -
        b * ((I.1.1.card : ℝ) * minor T I + rowExchange (minor T) I) +
        b * ((∑ i : Tail m, ∑ j : Tail n, T i j) * minor T I - raising (minor T) I)) := by
    calc
      _ = minor (T + x • Matrix.vecMulVec
          (fun i : Tail m => 1 - ∑ j : Tail n, T i j)
          (fun j : Tail n => 1 - b * ∑ i : Tail m, T i j)) I :=
        congrArg (fun U : Matrix (Tail m) (Tail n) ℝ => minor U I)
          (schur_rank_one_reconstruction hm hn S hS hB)
      _ = minor T I + x * cofactorForm T I (Matrix.vecMulVec
          (fun i : Tail m => 1 - ∑ j : Tail n, T i j)
          (fun j : Tail n => 1 - b * ∑ i : Tail m, T i j)) :=
        universal_rank_one_update T
          (fun i : Tail m => 1 - ∑ j : Tail n, T i j)
          (fun j : Tail n => 1 - b * ∑ i : Tail m, T i j) x I
      _ = _ := by
        rw [cofactorForm_outer_sub, minor_lowering_identity,
          hcolumn, hrow, minor_raising_identity]
  rw [htotal] at hminor
  rw [hminor, hdelta, raising_smul, lowering_smul, columnExchange_smul, rowExchange_smul]
  dsimp only [b]
  field_simp
  ring

#print axioms balanced_minor_relation
#assert_trust kernel balanced_minor_relation

end
end NLA.NM04
