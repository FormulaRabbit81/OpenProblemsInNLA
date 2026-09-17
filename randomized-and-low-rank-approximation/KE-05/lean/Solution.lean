import NLA.KE05.Asymptotic
import LeanCert.Tactic.Verification

/- Full KE-05 solution. Mathematical argument: George Stepaniants; original
framework: Nian Shao. Formalization: Sidney Holden with AI assistance. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace NLA.KE05

theorem literal_recurrence_contract {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i : Fin d) :
    (List.finRange d).map (rootOrder k) = k :: (List.finRange d).erase k ∧
    (recurrence L w k).lastS i = prefixS L w k i (recurrence L w k).hat (d - 1) ∧
    (recurrence L w k).hat i =
      (omega w (rootOrder k i) * (recurrence L w k).lastS i)⁻¹ *
      Matrix.diagonal (L (rootOrder k i)) *
      (omega w (rootOrder k i) * (recurrence L w k).lastS i) := by exact literal_recurrence_contract_proved L w k i

theorem admissibility_and_endpoints (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    Admissible (witnessData e) ∧ lowerEndpoint (witnessData e) = 0 ∧
    upperEndpoint (witnessData e) = 2 ∧ crossGap (witnessData e) 0 = 1 := by exact admissibility_and_endpoints_proved e he

theorem exact_rational_witness :
    X rationalSample = !![1, 0; 0, 2] ∧
    P rationalSample = !![6, 10; -3, -5] ∧
    kappa rationalSample = 7 ∧ Q rationalSample = !![30, 50; -18, -30] ∧
    spectralNorm (limitMatrix rationalSample) = (68 : ℝ) / 7 := by exact exact_rational_witness_proved

theorem probability_one_validity {b d : ℕ} (hb : 1 ≤ b) (hd : 2 ≤ d)
    (L : Data b d) (hL : Admissible L) :
    (∀ᵐ w ∂gaussianLaw b d, Valid L w) ∧ Measurable (totalConstant L) := by exact probability_one_validity_proved hb hd L hL

theorem probability_one_nonzero_limit :
    ∀ᵐ w ∂gaussianLaw 2 3,
      kappa w ≠ 0 ∧ Q w 0 0 ≠ 0 ∧
      (∀ m : ℕ, Valid (witnessData (epsilon m)) w) ∧
      Tendsto (fun m : ℕ => (recurrence (witnessData (epsilon m)) w 0).hat 1)
        atTop (nhds (limitMatrix w)) ∧ 0 < spectralNorm (limitMatrix w) := by exact probability_one_nonzero_limit_proved

theorem literal_lower_bound (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4)
    (w : Sample 2 3) (hw : Valid (witnessData e) w) :
    Real.rpow 8 (-(1 : ℝ) / 4) *
      (spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2 * e)) ≤
        totalConstant (witnessData e) w := by exact literal_lower_bound_proved e he w hw

theorem almost_sure_divergence :
    ∀ᵐ w ∂gaussianLaw 2 3,
      Tendsto (fun m : ℕ => totalConstant (witnessData (epsilon m)) w) atTop atTop := by exact almost_sure_divergence_proved

theorem marginal_probability_limit (C : ℝ) :
    Tendsto (fun m : ℕ => boundedProbability (witnessData (epsilon m)) C)
      atTop (nhds 0) := by exact marginal_probability_limit_proved C

theorem no_finite_uniform_constant :
    ∀ C : ℝ, ∃ L : Data 2 3,
      Admissible L ∧ boundedProbability L C < (1 : ℝ) / 2 := by exact no_finite_uniform_constant_proved

theorem not_uniform_probability_conjecture : ¬ UniformProbabilityConjecture := by exact not_uniform_probability_conjecture_proved

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
