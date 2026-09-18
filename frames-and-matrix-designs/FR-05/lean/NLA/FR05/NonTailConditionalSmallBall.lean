/-
The non-tail conditional small-ball branch of source Lemma 3.6.

The source splits on the deterministic scalar phase term
`sigma / 2 + beta cos(phi) - gamma sin(phi)`.  Away from its small
sublevel set, a Gaussian interval estimate uniform in the variance controls
the tail perturbation.  This module proves that elementary scalar-Gaussian
input and its product-phase assembly, before the outer radial mixture.
-/
import NLA.FR05.PhaseAbsolute
import NLA.FR05.TailConditionalSmallBall
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace NLA.FR05

lemma sqrt_mul_exp_neg_le_one (z : ℝ) (hz : 0 ≤ z) :
    Real.sqrt z * Real.exp (-z) ≤ 1 := by
  by_cases hz1 : z ≤ 1
  · have hsqrt : Real.sqrt z ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hz1
    have hexp : Real.exp (-z) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    calc
      Real.sqrt z * Real.exp (-z) ≤ 1 * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hsqrt (le_of_lt (Real.exp_pos _))
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hexp zero_le_one
      _ = 1 := by ring
  · have h1z : 1 ≤ z := le_of_not_ge hz1
    have hsqrt : Real.sqrt z ≤ z := by
      have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
      nlinarith [Real.sqrt_nonneg z]
    have hze : z ≤ Real.exp z := by
      have h := Real.add_one_le_exp z
      linarith
    have hprod : z * Real.exp (-z) ≤ 1 := by
      calc
        z * Real.exp (-z) ≤ Real.exp z * Real.exp (-z) :=
          mul_le_mul_of_nonneg_right hze (le_of_lt (Real.exp_pos _))
        _ = 1 := by rw [← Real.exp_add]; ring_nf; norm_num
    calc
      Real.sqrt z * Real.exp (-z) ≤ z * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hsqrt (le_of_lt (Real.exp_pos _))
      _ ≤ 1 := hprod

lemma exp_neg_div_sqrt_variance_le (t r : ℝ)
    (ht : 0 < t) (hr : 0 < r) :
    (Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r))) ≤ 3 / t := by
  let z : ℝ := t ^ 2 / (8 * r)
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hcore : Real.sqrt z * Real.exp (-z) ≤ 1 := sqrt_mul_exp_neg_le_one z hz
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsqrt8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hrootz : Real.sqrt z = t / (Real.sqrt 8 * Real.sqrt r) := by
    dsimp [z]
    rw [Real.sqrt_div (sq_nonneg t)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  have hroot8 : Real.sqrt 8 ≤ 3 := by
    exact (Real.sqrt_le_iff).mpr (by norm_num)
  have hmain : (Real.sqrt r)⁻¹ * Real.exp (-z) ≤ Real.sqrt 8 / t := by
    rw [hrootz] at hcore
    have hfactor : 0 ≤ Real.sqrt 8 / t :=
      (div_pos hsqrt8 ht).le
    have heq : (Real.sqrt r)⁻¹ * Real.exp (-z) =
        (Real.sqrt 8 / t) *
          ((t / (Real.sqrt 8 * Real.sqrt r)) * Real.exp (-z)) := by
      field_simp [hsqrtr.ne', hsqrt8.ne', ht.ne']
    rw [heq]
    calc
      (Real.sqrt 8 / t) *
          ((t / (Real.sqrt 8 * Real.sqrt r)) * Real.exp (-z)) ≤
          (Real.sqrt 8 / t) * 1 :=
        mul_le_mul_of_nonneg_left hcore hfactor
      _ = Real.sqrt 8 / t := by ring
  calc
    (Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r))) =
        (Real.sqrt r)⁻¹ * Real.exp (-z) := by rfl
    _ ≤ Real.sqrt 8 / t := hmain
    _ ≤ 3 / t := by
      exact div_le_div_of_nonneg_right hroot8 ht.le

lemma gaussianPDFReal_zero_le_three_div_of_abs_ge_half
    (t x : ℝ) {v : ℝ≥0} (ht : 0 < t) (hv : v ≠ 0)
    (hx : t / 2 ≤ |x|) :
    gaussianPDFReal 0 v x ≤ 3 / (Real.sqrt (2 * Real.pi) * t) := by
  let r : ℝ := (v : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have htwoPi : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 Real.two_pi_pos
  have hrootden : Real.sqrt (2 * Real.pi * r) =
      Real.sqrt (2 * Real.pi) * Real.sqrt r :=
    Real.sqrt_mul htwoPi r
  have hxsq : (t / 2) ^ 2 ≤ x ^ 2 := by
    have habsSq : (t / 2) ^ 2 ≤ |x| ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (abs_nonneg x)).mpr hx
    simpa only [sq_abs] using habsSq
  have hdiv : t ^ 2 / (8 * r) ≤ x ^ 2 / (2 * r) := by
    calc
      t ^ 2 / (8 * r) = (t / 2) ^ 2 / (2 * r) := by
        field_simp [hr.ne']
        ring
      _ ≤ x ^ 2 / (2 * r) :=
        div_le_div_of_nonneg_right hxsq (by positivity)
  have hexp' : Real.exp (-(x ^ 2 / (2 * r))) ≤
      Real.exp (-(t ^ 2 / (8 * r))) :=
    Real.exp_le_exp.mpr (neg_le_neg hdiv)
  have hexp : Real.exp (-x ^ 2 / (2 * r)) ≤
      Real.exp (-(t ^ 2 / (8 * r))) := by
    convert hexp' using 1
    ring
  rw [gaussianPDFReal]
  change (Real.sqrt (2 * Real.pi * r))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * r)) ≤
        3 / (Real.sqrt (2 * Real.pi) * t)
  simp only [sub_zero]
  rw [hrootden, mul_inv_rev]
  calc
    (Real.sqrt r)⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-x ^ 2 / (2 * r)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ((Real.sqrt r)⁻¹ * Real.exp (-x ^ 2 / (2 * r))) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
        ((Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r)))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hsqrtr.le)
      · exact inv_nonneg.mpr hsqrtTwoPi.le
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (3 / t) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_sqrt_variance_le t r ht hr)
        (inv_nonneg.mpr hsqrtTwoPi.le)
    _ = 3 / (Real.sqrt (2 * Real.pi) * t) := by
      field_simp [hsqrtTwoPi.ne', ht.ne']

/-- A Gaussian interval centred at `-m`, uniformly over its (possibly zero)
variance, is small when the centre is separated from zero.  The deliberately
coarse constant is enough for the source's non-tail `u^(1/3)` balance. -/
theorem gaussianReal_abs_add_smallBall_uniform
    (m u t : ℝ) {v : ℝ≥0} (ht : 0 < t)
    (hcentre : t ≤ |m|) (hscale : 2 * u ≤ t) :
    gaussianReal 0 v {x : ℝ | |m + x| ≤ u} ≤
      ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let s : Set ℝ := {x : ℝ | |m + x| ≤ u}
  have hs : s = Icc (-m - u) (-m + u) := by
    ext x
    dsimp [s]
    rw [Set.mem_Icc]
    constructor
    · intro hx
      have h := abs_le.mp hx
      constructor <;> linarith
    · rintro ⟨hl, hr⟩
      apply abs_le.mpr
      constructor <;> linarith
  change gaussianReal 0 v s ≤ _
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    have hnot : (0 : ℝ) ∉ s := by
      intro hzero
      dsimp [s] at hzero
      have hlt : u < t := by linarith
      have hm : |m| ≤ u := by simpa using hzero
      linarith
    have hdirac : Measure.dirac (0 : ℝ) s = 0 := by
      rw [MeasureTheory.Measure.dirac_apply]
      simp only [Set.indicator, hnot, if_false]
    rw [hdirac]
    exact bot_le
  · rw [gaussianReal_apply 0 hv s]
    have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.2 Real.two_pi_pos
    have hpoint : ∀ x : ℝ, x ∈ s →
        gaussianPDF 0 v x ≤
          ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) := by
      intro x hx
      have hxbound : |m + x| ≤ u := by
        simpa only [s, Set.mem_ofPred_eq] using hx
      have hmx : |m| ≤ u + |x| := by
        calc
          |m| = |(m + x) - x| := by
            congr 1
            ring
          _ ≤ |m + x| + |x| := by
            exact abs_sub (m + x) x
          _ ≤ u + |x| := by
            linarith
      have hhalf : t / 2 ≤ |x| := by linarith
      change ENNReal.ofReal (gaussianPDFReal 0 v x) ≤ _
      exact ENNReal.ofReal_le_ofReal
        (gaussianPDFReal_zero_le_three_div_of_abs_ge_half t x ht hv hhalf)
    calc
      ∫⁻ x in s, gaussianPDF 0 v x ≤
          ∫⁻ _x in s, ENNReal.ofReal
            (3 / (Real.sqrt (2 * Real.pi) * t)) :=
        MeasureTheory.setLIntegral_mono_ae (by fun_prop)
          (Filter.Eventually.of_forall fun x hx ↦ hpoint x hx)
      _ = ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) * volume s :=
        setLIntegral_const s _
      _ = ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) *
          ENNReal.ofReal (2 * u) := by
        rw [hs, Real.volume_Icc]
        congr 2
        ring
      _ = ENNReal.ofReal
          ((3 / (Real.sqrt (2 * Real.pi) * t)) * (2 * u)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
        congr 1
        field_simp [hsqrtTwoPi.ne', ht.ne']
        ring

/-- The literal source scalar term from equation (3.21), plus an independent
real Gaussian perturbation.  This is the non-tail conditional event before
the outer radial mixture is introduced. -/
def sourceScalarGaussianSmallBallEvent
    (σ β γ u : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |sourceScalarPhase σ β γ x.1 + x.2| ≤ u}

theorem measurableSet_sourceScalarGaussianSmallBallEvent
    (σ β γ u : ℝ) :
    MeasurableSet (sourceScalarGaussianSmallBallEvent σ β γ u) := by
  unfold sourceScalarGaussianSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × ℝ => |sourceScalarPhase σ β γ x.1 + x.2|) ⁻¹' Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    unfold sourceScalarPhase
    fun_prop

/-- The source's second conditional branch, after splitting phase into the
small deterministic-scalar set and its complement.  The Gaussian interval
bound is uniform in its variance, so the result includes the degenerate
variance case.  The resulting two terms are exactly balanced by
`t = u^(2/3)` in the informal source proof. -/
theorem sourceUniformInterval_prod_sourceScalarGaussianSmallBall_le
    (σ β γ u t : ℝ) {v : ℝ≥0}
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (gaussianReal 0 v))
        (sourceScalarGaussianSmallBallEvent σ β γ u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let hgaussian : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
  apply @prod_measure_le_add_of_bad_sections ℝ ℝ _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (gaussianReal 0 v) hphase hgaussian
    (sourceScalarGaussianSmallBallEvent σ β γ u)
    (measurableSet_sourceScalarGaussianSmallBallEvent σ β γ u)
    (sourceScalarPhaseSublevel σ β γ t)
    (measurableSet_sourceScalarPhaseSublevel σ β γ t)
    (ENNReal.ofReal (2 * Real.sqrt (2 * t)))
    (ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)))
  · exact sourceUniformInterval_sourceScalarPhaseSublevel_le_two_sqrt_two_mul
      σ β γ t ht.le hcoeff
  · intro φ hφ
    by_cases hsupport : φ ∈ Icc 0 (2 * Real.pi)
    · have hnotle : ¬ |sourceScalarPhase σ β γ φ| ≤ t := by
        intro hle
        exact hφ ⟨hsupport, hle⟩
      have hcentre : t ≤ |sourceScalarPhase σ β γ φ| :=
        (lt_of_not_ge hnotle).le
      change gaussianReal 0 v
          {w : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
            |sourceScalarPhase σ β γ φ + w| ≤ u} ≤ _
      simp only [hsupport, true_and]
      exact gaussianReal_abs_add_smallBall_uniform
        (sourceScalarPhase σ β γ φ) u t ht hcentre hscale
    · have hempty :
        {w : ℝ | (φ, w) ∈ sourceScalarGaussianSmallBallEvent σ β γ u} = ∅ := by
          ext w
          change (φ ∈ Icc 0 (2 * Real.pi) ∧
            |sourceScalarPhase σ β γ φ + w| ≤ u) ↔ w ∈ (∅ : Set ℝ)
          simp only [hsupport, false_and]
          exact (Set.mem_empty_iff_false w).symm
      rw [hempty, measure_empty]
      exact bot_le

/-- The source choice `t = u^(2/3)` written without real-power machinery:
put `u = r^3` and `t = r^2`.  For `0 < r ≤ 1/2`, the non-tail conditional
probability is explicitly bounded by a fixed constant times `r`, i.e.
by `O(u^(1/3))`. -/
theorem sourceUniformInterval_prod_sourceScalarGaussianSmallBall_cubic_le
    (σ β γ r : ℝ) {v : ℝ≥0}
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (gaussianReal 0 v))
        (sourceScalarGaussianSmallBallEvent σ β γ (r ^ 3)) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * r) +
        ENNReal.ofReal (6 * r / Real.sqrt (2 * Real.pi)) := by
  have hscale : 2 * r ^ 3 ≤ r ^ 2 := by
    calc
      2 * r ^ 3 = (2 * r) * r ^ 2 := by ring
      _ ≤ 1 * r ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact sq_nonneg r
      _ = r ^ 2 := by ring
  have hmain := sourceUniformInterval_prod_sourceScalarGaussianSmallBall_le
    σ β γ (r ^ 3) (r ^ 2) (sq_pos_of_pos hr) hscale hcoeff (v := v)
  have hsqrt : Real.sqrt (2 * r ^ 2) = Real.sqrt 2 * r := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.two_pi_pos)
  have hratio :
      6 * r ^ 3 / (Real.sqrt (2 * Real.pi) * r ^ 2) =
        6 * r / Real.sqrt (2 * Real.pi) := by
    field_simp [hsqrtTwoPi, hr.ne']
  rw [hsqrt, hratio] at hmain
  simpa only [mul_assoc] using hmain

end NLA.FR05
