import NLA.KE05.PolynomialNull

/- Rational expressions regular at a deterministic witness. Denominators remain
explicit polynomials; inversion is admitted only when its actual witness value is
nonzero. These are proof-building lemmas, not assumptions on Gaussian samples. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NLA.KE05

inductive RegularAt {σ : Type*} (a : σ → ℝ) : ((σ → ℝ) → ℝ) → Prop
  | const (c : ℝ) : RegularAt a (fun _ => c)
  | coord (i : σ) : RegularAt a (fun x => x i)
  | add {f g} : RegularAt a f → RegularAt a g → RegularAt a (fun x => f x + g x)
  | mul {f g} : RegularAt a f → RegularAt a g → RegularAt a (fun x => f x * g x)
  | inv {f} : RegularAt a f → f a ≠ 0 → RegularAt a (fun x => (f x)⁻¹)

lemma RegularAt.neg {σ : Type*} {a : σ → ℝ} {f} (hf : RegularAt a f) :
    RegularAt a (fun x => -f x) := by
  simpa using (RegularAt.const (-1)).mul hf

lemma RegularAt.sub {σ : Type*} {a : σ → ℝ} {f g} (hf : RegularAt a f)
    (hg : RegularAt a g) : RegularAt a (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma RegularAt.measurable {σ : Type*} {a : σ → ℝ} {f} (hf : RegularAt a f) :
    Measurable f := by
  induction hf with
  | const c => exact measurable_const
  | coord i => exact measurable_pi_apply i
  | add _ _ ihf ihg => exact ihf.add ihg
  | mul _ _ ihf ihg => exact ihf.mul ihg
  | inv _ _ ih => exact ih.inv

lemma RegularAt.rational_rep {σ : Type*} {a : σ → ℝ} {f} (hf : RegularAt a f) :
    ∃ p q : MvPolynomial σ ℝ, MvPolynomial.eval a q ≠ 0 ∧
      ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p / MvPolynomial.eval x q := by
  induction hf with
  | const c => exact ⟨MvPolynomial.C c, 1, by simp, by simp⟩
  | coord i => exact ⟨MvPolynomial.X i, 1, by simp, by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p,q,hq,hf⟩ := ihf
    obtain ⟨r,s,hs,hg⟩ := ihg
    refine ⟨p*s+r*q,q*s,by simpa using mul_ne_zero hq hs,?_⟩
    intro x hx
    have hh : MvPolynomial.eval x q ≠ 0 ∧ MvPolynomial.eval x s ≠ 0 := by simpa using hx
    dsimp only
    rw [hf x hh.1, hg x hh.2]
    simp only [map_add, map_mul]
    field_simp [hh.1, hh.2] <;> ring
  | mul _ _ ihf ihg =>
    obtain ⟨p,q,hq,hf⟩ := ihf
    obtain ⟨r,s,hs,hg⟩ := ihg
    refine ⟨p*r,q*s,by simpa using mul_ne_zero hq hs,?_⟩
    intro x hx
    have hh : MvPolynomial.eval x q ≠ 0 ∧ MvPolynomial.eval x s ≠ 0 := by simpa using hx
    dsimp only
    rw [hf x hh.1, hg x hh.2]
    simp only [map_mul]
    exact div_mul_div_comm _ _ _ _
  | inv h hn ih =>
    obtain ⟨p,q,hq,hf⟩ := ih
    have hp : MvPolynomial.eval a p ≠ 0 := by
      intro hp
      apply hn
      rw [hf a hq, hp, zero_div]
    refine ⟨q*q,p*q,by simpa using mul_ne_zero hp hq,?_⟩
    intro x hx
    have hh : MvPolynomial.eval x p ≠ 0 ∧ MvPolynomial.eval x q ≠ 0 := by simpa using hx
    dsimp only
    rw [hf x hh.2]
    simp only [map_mul, inv_div]
    field_simp [hh.1, hh.2] <;> ring

lemma RegularAt.sum {σ ι : Type*} {a : σ → ℝ} (s : Finset ι)
    (f : ι → (σ → ℝ) → ℝ) (hf : ∀ i ∈ s, RegularAt a (f i)) :
    RegularAt a (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegularAt.const (a := a) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

lemma RegularAt.prod {σ ι : Type*} {a : σ → ℝ} (s : Finset ι)
    (f : ι → (σ → ℝ) → ℝ) (hf : ∀ i ∈ s, RegularAt a (f i)) :
    RegularAt a (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegularAt.const (a := a) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (by simp)).mul (ih (fun j hj => hf j (by simp [hj])))

lemma RegularAt.ae_ne_zero {σ : Type*} [Fintype σ] {a : σ → ℝ} {f}
    (hf : RegularAt a f) (ha : f a ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : σ => ProbabilityTheory.gaussianReal 0 1), f x ≠ 0 := by
  obtain ⟨p,q,hq,he⟩ := hf.rational_rep
  have hp : p ≠ 0 := by
    intro hp
    apply ha
    rw [he a hq, hp, map_zero, zero_div]
  have hq' : q ≠ 0 := by
    intro hz
    apply hq
    simp [hz]
  filter_upwards [gaussian_polynomial_ae_ne_zero p hp,
    gaussian_polynomial_ae_ne_zero q hq'] with x hpx hqx
  rw [he x hqx]
  exact div_ne_zero hpx hqx

end NLA.KE05
