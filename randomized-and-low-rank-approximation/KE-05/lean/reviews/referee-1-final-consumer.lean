/- Statements only. Deliberate placeholders establish no result and must never
be imported by a future Solution. -/
import Solution
import LeanCert.Tactic.Verification
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace NLA.KE05

theorem referee_one_literal_recurrence_contract {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i : Fin d) :
    (List.finRange d).map (rootOrder k) = k :: (List.finRange d).erase k ∧
    (recurrence L w k).lastS i = prefixS L w k i (recurrence L w k).hat (d - 1) ∧
    (recurrence L w k).hat i =
      (omega w (rootOrder k i) * (recurrence L w k).lastS i)⁻¹ *
      Matrix.diagonal (L (rootOrder k i)) *
      (omega w (rootOrder k i) * (recurrence L w k).lastS i) := by apply literal_recurrence_contract <;> assumption

theorem referee_one_admissibility_and_endpoints (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    Admissible (witnessData e) ∧ lowerEndpoint (witnessData e) = 0 ∧
    upperEndpoint (witnessData e) = 2 ∧ crossGap (witnessData e) 0 = 1 := by apply admissibility_and_endpoints <;> assumption

theorem referee_one_exact_rational_witness :
    X rationalSample = !![1, 0; 0, 2] ∧
    P rationalSample = !![6, 10; -3, -5] ∧
    kappa rationalSample = 7 ∧ Q rationalSample = !![30, 50; -18, -30] ∧
    spectralNorm (limitMatrix rationalSample) = (68 : ℝ) / 7 := by apply exact_rational_witness <;> assumption

theorem referee_one_probability_one_validity {b d : ℕ} (hb : 1 ≤ b) (hd : 2 ≤ d)
    (L : Data b d) (hL : Admissible L) :
    (∀ᵐ w ∂gaussianLaw b d, Valid L w) ∧ Measurable (totalConstant L) := by apply probability_one_validity <;> assumption

theorem referee_one_probability_one_nonzero_limit :
    ∀ᵐ w ∂gaussianLaw 2 3,
      kappa w ≠ 0 ∧ Q w 0 0 ≠ 0 ∧
      (∀ m : ℕ, Valid (witnessData (epsilon m)) w) ∧
      Tendsto (fun m : ℕ => (recurrence (witnessData (epsilon m)) w 0).hat 1)
        atTop (nhds (limitMatrix w)) ∧ 0 < spectralNorm (limitMatrix w) := by apply probability_one_nonzero_limit <;> assumption

theorem referee_one_literal_lower_bound (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4)
    (w : Sample 2 3) (hw : Valid (witnessData e) w) :
    Real.rpow 8 (-(1 : ℝ) / 4) *
      (spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2 * e)) ≤
        totalConstant (witnessData e) w := by apply literal_lower_bound <;> assumption

theorem referee_one_almost_sure_divergence :
    ∀ᵐ w ∂gaussianLaw 2 3,
      Tendsto (fun m : ℕ => totalConstant (witnessData (epsilon m)) w) atTop atTop := by apply almost_sure_divergence <;> assumption

theorem referee_one_marginal_probability_limit (C : ℝ) :
    Tendsto (fun m : ℕ => boundedProbability (witnessData (epsilon m)) C)
      atTop (nhds 0) := by apply marginal_probability_limit <;> assumption

theorem referee_one_no_finite_uniform_constant :
    ∀ C : ℝ, ∃ L : Data 2 3,
      Admissible L ∧ boundedProbability L C < (1 : ℝ) / 2 := by apply no_finite_uniform_constant <;> assumption

theorem referee_one_not_uniform_probability_conjecture : ¬ UniformProbabilityConjecture := by apply not_uniform_probability_conjecture <;> assumption

end NLA.KE05
end

#print axioms NLA.KE05.literal_recurrence_contract
#assert_trust kernel NLA.KE05.literal_recurrence_contract
#print axioms NLA.KE05.admissibility_and_endpoints
#assert_trust kernel NLA.KE05.admissibility_and_endpoints
#print axioms NLA.KE05.exact_rational_witness
#assert_trust kernel NLA.KE05.exact_rational_witness
#print axioms NLA.KE05.probability_one_validity
#assert_trust kernel NLA.KE05.probability_one_validity
#print axioms NLA.KE05.probability_one_nonzero_limit
#assert_trust kernel NLA.KE05.probability_one_nonzero_limit
#print axioms NLA.KE05.literal_lower_bound
#assert_trust kernel NLA.KE05.literal_lower_bound
#print axioms NLA.KE05.almost_sure_divergence
#assert_trust kernel NLA.KE05.almost_sure_divergence
#print axioms NLA.KE05.marginal_probability_limit
#assert_trust kernel NLA.KE05.marginal_probability_limit
#print axioms NLA.KE05.no_finite_uniform_constant
#assert_trust kernel NLA.KE05.no_finite_uniform_constant
#print axioms NLA.KE05.not_uniform_probability_conjecture
#assert_trust kernel NLA.KE05.not_uniform_probability_conjecture
