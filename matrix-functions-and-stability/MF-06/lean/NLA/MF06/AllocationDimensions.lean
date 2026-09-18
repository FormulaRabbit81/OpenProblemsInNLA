/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Literal coordinate fibers partition the original dimension. Every allocation
factor has a nonempty exterior basis, including degree zero and empty fibers.
Equal-degree distinct allocations have strictly different max/min degrees;
the proof uses finite-sum rigidity, with no tie-breaking or enumeration.
-/
import NLA.MF06.CompoundAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma sum_blockDim {d r : ℕ} (b : Fin d → Fin r) :
    (∑ i : Fin r, blockDim b i) = d := by
  simpa only [Fintype.card_sigma, Fintype.card_fin, blockDim] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv b)

theorem allocation_dimensions {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    (∑ i : Fin r, blockDim b i) = d ∧
    allocationDegree b a ≤ d ∧ 1 ≤ allocationDim b a := by
  refine ⟨sum_blockDim b, ?_, ?_⟩
  · calc
      allocationDegree b a ≤ ∑ i : Fin r, blockDim b i :=
        Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (a i).isLt
      _ = d := sum_blockDim b
  · change 0 < Fintype.card (AllocationIndex b a)
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun i => ⟨0, Nat.zero_lt_one.trans_le
      ((compound_dimensions (blockDim b i) (a i).val).2 (Nat.le_of_lt_succ (a i).isLt))⟩⟩

lemma allocation_eq_of_le_degree_eq {d r : ℕ} {b : Fin d → Fin r}
    (a c : Allocation b) (hle : ∀ i, a i ≤ c i)
    (heq : allocationDegree b a = allocationDegree b c) : a = c := by
  have hsum : (∑ i : Fin r, (a i).val) = ∑ i : Fin r, (c i).val := heq
  have hcoord := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => Fin.le_def.mp (hle i))).mp hsum
  funext i
  exact Fin.ext (hcoord i (Finset.mem_univ _))

theorem distinct_allocation_degrees {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (a c : DegreeAllocation b k) (hne : a ≠ c) :
    k < allocationDegree b (allocationMax a.val c.val) ∧
    allocationDegree b (allocationMin a.val c.val) < k := by
  have hmax : k ≤ allocationDegree b (allocationMax a.val c.val) := by
    calc
      k = allocationDegree b a.val := a.property.symm
      _ ≤ allocationDegree b (allocationMax a.val c.val) :=
        Finset.sum_le_sum fun i _ => Fin.le_def.mp (le_max_left (a.val i) (c.val i))
  have hneMax : k ≠ allocationDegree b (allocationMax a.val c.val) := by
    intro heq
    have ha : a.val = allocationMax a.val c.val := allocation_eq_of_le_degree_eq
      a.val (allocationMax a.val c.val) (fun i => le_max_left _ _) (a.property.trans heq)
    have hc : c.val = allocationMax a.val c.val := allocation_eq_of_le_degree_eq
      c.val (allocationMax a.val c.val) (fun i => le_max_right _ _) (c.property.trans heq)
    exact hne (Subtype.ext (ha.trans hc.symm))
  have hstrict := lt_of_le_of_ne hmax hneMax
  have hsum : allocationDegree b (allocationMin a.val c.val) +
      allocationDegree b (allocationMax a.val c.val) = k + k := by
    have hpoint (i : Fin r) :
        (allocationMin a.val c.val i).val + (allocationMax a.val c.val i).val =
          (a.val i).val + (c.val i).val := by
      rcases le_total (a.val i) (c.val i) with h | h
      · simp only [allocationMin, allocationMax, min_eq_left h, max_eq_right h]
      · simp only [allocationMin, allocationMax, min_eq_right h, max_eq_left h]
        omega
    calc
      allocationDegree b (allocationMin a.val c.val) +
          allocationDegree b (allocationMax a.val c.val) =
          ∑ i : Fin r, ((allocationMin a.val c.val i).val +
            (allocationMax a.val c.val i).val) := Finset.sum_add_distrib.symm
      _ = ∑ i : Fin r, ((a.val i).val + (c.val i).val) :=
        Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = allocationDegree b a.val + allocationDegree b c.val := Finset.sum_add_distrib
      _ = k + k := congrArg₂ (· + ·) a.property c.property
  exact ⟨hstrict, by omega⟩

#print axioms allocation_dimensions
#assert_trust kernel allocation_dimensions
#print axioms distinct_allocation_degrees
#assert_trust kernel distinct_allocation_degrees

end NLA.MF06
