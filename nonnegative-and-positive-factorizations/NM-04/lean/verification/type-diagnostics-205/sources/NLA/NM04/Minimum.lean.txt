/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

Existence of a minimum of the actual scaling potential. Positive matrix
entries have a uniform positive lower bound, so the proved coercivity bound
makes each closed sublevel in the zero-sum hyperplane compact. The extreme
value theorem then supplies a global minimizer on that hyperplane.
-/
import NLA.NM04.Coercivity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
open scoped BigOperators

/-- Positivity on a finite nonempty rectangle gives an attained, strictly
positive common lower bound, without a numerical minimum computation. -/
theorem positive_matrix_uniform_lower_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    ∃ a : ℝ, 0 < a ∧ ∀ i j, a ≤ A i j := by
  classical
  obtain ⟨ij, _hij, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin m × Fin n))
      (fun ij => A ij.1 ij.2)
      ⟨(firstIndex hm, firstIndex hn), Finset.mem_univ _⟩
  exact ⟨A ij.1 ij.2, hA ij.1 ij.2,
    fun i j => hmin (i, j) (Finset.mem_univ _)⟩

theorem zero_mem_meanZero (n : ℕ) : (0 : Fin n → ℝ) ∈ meanZero n := by
  simp [meanZero]

/-- The zero-sum constraint is a closed equality of continuous functions. -/
theorem meanZero_isClosed (n : ℕ) : IsClosed (meanZero n) := by
  unfold meanZero
  exact isClosed_eq
    (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

/-- Every sublevel of the actual potential on the zero-sum hyperplane is
compact, including empty sublevels. The radius is symbolic and unrestricted. -/
theorem potential_sublevel_isCompact {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (r : ℝ) :
    IsCompact (meanZero n ∩ {t : Fin n → ℝ | potential A t ≤ r}) := by
  obtain ⟨a, ha, haA⟩ := positive_matrix_uniform_lower_bound hm hn A hA
  let c : ℝ := (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ))
  have hm_pos : (0 : ℝ) < (m : ℝ) :=
    zero_lt_one.trans_le (Nat.one_le_cast.mpr hm)
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    zero_lt_one.trans_le (Nat.one_le_cast.mpr hn)
  have hc : 0 < c := mul_pos coercivity_half_certificate.1 (div_pos hm_pos hn_pos)
  have hclosed : IsClosed (meanZero n ∩ {t : Fin n → ℝ | potential A t ≤ r}) :=
    (meanZero_isClosed n).inter
      (isClosed_le (potential_continuous hn A hA) continuous_const)
  have hbounded : Bornology.IsBounded
      (meanZero n ∩ {t : Fin n → ℝ | potential A t ≤ r}) := by
    refine isBounded_iff_forall_norm_le.mpr
      ⟨(r - (m : ℝ) * Real.log a) / c, ?_⟩
    intro t ht
    have hcoercive : c * ‖t‖ + (m : ℝ) * Real.log a ≤ potential A t :=
      zero_mean_coercivity hn A a ha haA t ht.1
    have hvalue : potential A t ≤ r := ht.2
    have hscaled : c * ‖t‖ ≤ r - (m : ℝ) * Real.log a := by
      linarith only [hcoercive, hvalue]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm c ‖t‖] using hscaled
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

theorem potential_attains_minimum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    ∃ t₀ : Fin n → ℝ, t₀ ∈ meanZero n ∧
      ∀ t : Fin n → ℝ, t ∈ meanZero n → potential A t₀ ≤ potential A t := by
  let K : Set (Fin n → ℝ) :=
    meanZero n ∩ {t : Fin n → ℝ | potential A t ≤ potential A 0}
  have hcompact : IsCompact K :=
    potential_sublevel_isCompact hm hn A hA (potential A 0)
  have hzero : (0 : Fin n → ℝ) ∈ K := by
    refine ⟨zero_mem_meanZero n, ?_⟩
    -- Unfold membership in the chosen sublevel at the zero vector.
    change potential A (0 : Fin n → ℝ) ≤ potential A 0
    exact le_rfl
  obtain ⟨t₀, ht₀, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩
    (potential_continuous hn A hA).continuousOn
  refine ⟨t₀, ht₀.1, ?_⟩
  intro t ht
  by_cases hsub : potential A t ≤ potential A 0
  · exact hmin ⟨ht, hsub⟩
  · exact ht₀.2.trans (not_le.mp hsub).le

#print axioms potential_attains_minimum
#assert_trust kernel potential_attains_minimum

end NLA.NM04
