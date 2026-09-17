/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.RetainedTrace
import NLA.RA02.HistoryIdentity

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma retained_prefix_product_bound (r : ℕ) (hr : 1 ≤ r) (bits : Fin r → Bool) :
    0 < prefixTraceProduct (arrowhead r) (List.ofFn (retainedHistory r bits)) ∧
    prefixTraceProduct (arrowhead r) (List.ofFn (retainedHistory r bits)) ≤
      (∏ i : Fin r, diagonalWeight r i.val) * (1 + 1 / (r : ℝ)) ^ r := by
  have hprod : prefixTraceProduct (arrowhead r) (List.ofFn (retainedHistory r bits)) =
      ∏ s : Fin r, realTrace (pathResidual (arrowhead r) (retainedPrefix r bits s.val)) := by
    unfold prefixTraceProduct retainedPrefix
    exact Fintype.prod_equiv (finCongr List.length_ofFn) _ _ (fun _ => rfl)
  rw [hprod]
  refine ⟨Finset.prod_pos (fun s _ => (retained_trace_bound r hr bits s.val s.isLt).1), ?_⟩
  calc
    (∏ s : Fin r, realTrace (pathResidual (arrowhead r) (retainedPrefix r bits s.val))) ≤
        ∏ s : Fin r, scaleParameter r ^ s.val * (1 + 1 / (r : ℝ)) :=
      Finset.prod_le_prod
        (fun s _ => (retained_trace_bound r hr bits s.val s.isLt).1.le)
        (fun s _ => (retained_trace_bound r hr bits s.val s.isLt).2)
    _ = (∏ i : Fin r, diagonalWeight r i.val) * (1 + 1 / (r : ℝ)) ^ r := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, diagonalWeight]

theorem retained_contribution_bound (r : ℕ) (hr : 1 ≤ r) (bits : Fin r → Bool) :
    scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r ≤
      pathContribution (arrowhead r) (List.ofFn (retainedHistory r bits)) := by
  have hpref := retained_prefix_product_bound r hr bits
  have hD : 0 < ∏ i : Fin r, diagonalWeight r i.val :=
    Finset.prod_pos (fun i _ => diagonalWeight_pos r i.val)
  have hB : 0 < (1 + 1 / (r : ℝ)) ^ r := by positivity
  have hE : 0 < scaleParameter r ^ r := pow_pos (scaleParameter_pos r) r
  have hid := (distinct_history_identity r hr (List.ofFn (retainedHistory r bits))
    ((retained_history_count r).2.2 bits) (List.length_ofFn)).2
  rw [hid, commonNumerator]
  calc
    scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r =
        (scaleParameter r ^ r * ∏ i : Fin r, diagonalWeight r i.val) /
          ((∏ i : Fin r, diagonalWeight r i.val) * (1 + 1 / (r : ℝ)) ^ r) := by
      field_simp [hD.ne', hB.ne'] <;> ring
    _ ≤ (scaleParameter r ^ r * ∏ i : Fin r, diagonalWeight r i.val) /
        prefixTraceProduct (arrowhead r) (List.ofFn (retainedHistory r bits)) :=
      div_le_div_of_nonneg_left (mul_nonneg hE.le hD.le) hpref.1 hpref.2

#print axioms retained_prefix_product_bound
#assert_trust kernel retained_prefix_product_bound
#print axioms retained_contribution_bound
#assert_trust kernel retained_contribution_bound

end
end NLA.RA02
