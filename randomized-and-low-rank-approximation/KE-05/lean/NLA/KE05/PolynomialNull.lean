import NLA.KE05.Definitions

/- Nonzero multivariate polynomials vanish with probability zero under finite
products of atomless measures. The induction/Fubini argument is the one used in
George Stepaniants's KE-05 proof; the univariate root and product APIs are Mathlib. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.KE05

lemma univariate_ae_ne_zero (μ : Measure ℝ) [NullSingletonClass μ]
    (p : Polynomial ℝ) (hp : p ≠ 0) : ∀ᵐ x ∂μ, p.eval x ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not, Polynomial.IsRoot.def] using
    (Polynomial.finite_setOfPred_isRoot hp).measure_zero μ

lemma polynomial_ae_ne_zero_fin (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ]
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
    apply Filter.Eventually.of_forall
    intro x hx
    apply hp
    apply MvPolynomial.funext
    intro y
    have hxy : y = x := Subsingleton.elim _ _
    simpa [hxy] using hx
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv ℝ n p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by simpa [q] using h)
    obtain ⟨k,hk⟩ : ∃ k, q.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      apply hq
      apply Polynomial.ext
      intro k
      simpa using h k
    have htail := ih (q.coeff k) hk
    have haa : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
        ∀ᵐ y ∂μ, MvPolynomial.eval (Fin.cons y x) p ≠ 0 := by
      filter_upwards [htail] with x hx
      have hm : Polynomial.map (MvPolynomial.eval x) q ≠ 0 := by
        intro h
        have hc := congrArg (fun r : Polynomial ℝ => r.coeff k) h
        apply hx
        simpa using hc
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', q] using
        univariate_ae_ne_zero μ (Polynomial.map (MvPolynomial.eval x) q) hm
    have hs : MeasurableSet {z : ℝ × (Fin n → ℝ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} := by
      apply (MeasurableSet.singleton 0).preimage ?_ |>.compl
      exact p.continuous_eval.measurable.comp (by fun_prop)
    have hprod : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : Fin n => μ)),
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hs).mpr ((Measure.ae_ae_comm hs).mpr haa)
    have hback := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => μ) 0).quasiMeasurePreserving.ae hprod
    filter_upwards [hback] with x hx
    convert hx using 1
    congr 2
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma polynomial_ae_ne_zero {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ]
    (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : σ => μ), MvPolynomial.eval x p ≠ 0 := by
  let e := Fintype.equivFin σ
  have hp' : MvPolynomial.rename e p ≠ 0 := by
    intro hz
    apply hp
    exact (MvPolynomial.rename_injective (R := ℝ) e e.injective) (by simpa using hz)
  have hh := polynomial_ae_ne_zero_fin μ (Fintype.card σ) (MvPolynomial.rename e p) hp'
  have hb := (measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => μ) e).quasiMeasurePreserving.ae hh
  filter_upwards [hb] with x hx
  simpa [MvPolynomial.eval_rename, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', Function.comp_def] using hx

lemma gaussian_polynomial_ae_ne_zero {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : σ => gaussianReal 0 1), MvPolynomial.eval x p ≠ 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact polynomial_ae_ne_zero (gaussianReal 0 1) p hp

end NLA.KE05
