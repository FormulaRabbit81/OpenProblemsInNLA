import NLA.RowDeletion.GaussianDensity

/-! # Gaussian direction and radius

The spherical law here is the normalized surface law fixed in `Definitions`.
Polar coordinates factor every radial probability density into that spherical
law and its actual radius marginal. Applying this to the standard Gaussian
proves both the direction law and radius/direction independence.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLA.RowDeletion

/-- Radial projection onto the unit sphere, with value zero at the origin. -/
def sphereDirection {n : ℕ} (x : Vector n) : Vector n := ‖x‖⁻¹ • x

@[fun_prop]
lemma measurable_sphereDirection (n : ℕ) : Measurable (@sphereDirection n) := by
  unfold sphereDirection
  fun_prop

lemma norm_smul_sphereDirection {n : ℕ} (x : Vector n) :
    ‖x‖ • sphereDirection x = x := by
  by_cases hx : x = 0
  · simp [hx, sphereDirection]
  · simp [sphereDirection, smul_smul, norm_ne_zero_iff.mpr hx]

/-- A radial probability density has uniform direction independent of its radius.
No evaluation of the radial normalizing integral is required. -/
theorem radial_probability_map_direction_norm {n : ℕ} (hn : 0 < n)
    (μ : Measure (Vector n)) [IsProbabilityMeasure μ]
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hμ : μ = volume.withDensity (fun x ↦ w ‖x‖)) :
    μ.map (fun x ↦ (sphereDirection x, ‖x‖)) =
      (sphericalLaw n).prod (μ.map (fun x ↦ ‖x‖)) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := (volume : Measure (Vector n)).toSphere
  let R := (Measure.volumeIoiPow (Module.finrank ℝ (Vector n) - 1)).withDensity
    (fun r : Set.Ioi (0 : ℝ) ↦ w r)
  let ρ := R.map (fun r : Set.Ioi (0 : ℝ) ↦ (r : ℝ))
  let σ' := σ.map (fun u : Metric.sphere (0 : Vector n) 1 ↦ (u : Vector n))
  have hcoe : (μ.comap (fun x : ({0}ᶜ : Set (Vector n)) ↦ (x : Vector n))).map
      (fun x : ({0}ᶜ : Set (Vector n)) ↦ (x : Vector n)) = μ := by
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl, hμ]
    exact restrict_compl_singleton 0
  have hpolar : (μ.comap (fun x : ({0}ᶜ : Set (Vector n)) ↦ (x : Vector n))).map
      (homeomorphUnitSphereProd (Vector n)) = σ.prod R := by
    rw [hμ]
    exact polar_map_radial_density n w hw
  have hjoint : μ.map (fun x ↦ (sphereDirection x, ‖x‖)) = σ'.prod ρ := by
    dsimp only [σ', ρ]
    rw [Measure.map_prod_map σ R measurable_subtype_coe measurable_subtype_coe,
      ← hpolar, Measure.map_map (by fun_prop) (by fun_prop)]
    conv_lhs => rw [← hcoe]
    rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
    congr 1
    funext x
    simp [Prod.map, sphereDirection]
  have hr : μ.map (fun x ↦ ‖x‖) = σ Set.univ • ρ := by
    have h := congrArg (Measure.map (Prod.snd : Vector n × ℝ → ℝ)) hjoint
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod] at h
    simpa [Function.comp_def, σ', Measure.map_apply measurable_subtype_coe MeasurableSet.univ] using h
  have hσ : σ Set.univ ≠ 0 := fun h ↦
    Measure.toSphere_ne_zero (volume : Measure (Vector n)) (Measure.measure_univ_eq_zero.mp h)
  rw [hjoint, hr, sphericalLaw, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  change σ'.prod ρ = ((σ Set.univ)⁻¹ * σ Set.univ) • (σ'.prod ρ)
  rw [ENNReal.inv_mul_cancel hσ (measure_ne_top σ Set.univ), one_smul]

/-- The joint law of Gaussian direction and radius factors as a product. -/
theorem stdGaussian_map_direction_norm {n : ℕ} (hn : 0 < n) :
    (stdGaussian (Vector n)).map (fun x ↦ (sphereDirection x, ‖x‖)) =
      (sphericalLaw n).prod ((stdGaussian (Vector n)).map (fun x ↦ ‖x‖)) :=
  radial_probability_map_direction_norm hn _ _ (measurable_gaussianRadialDensity n)
    (stdGaussian_eq_radial_density n)

/-- Normalizing a standard Gaussian gives exactly the specified surface law. -/
theorem stdGaussian_map_sphereDirection {n : ℕ} (hn : 0 < n) :
    (stdGaussian (Vector n)).map sphereDirection = sphericalLaw n := by
  have h := congrArg (Measure.map (Prod.fst : Vector n × ℝ → Vector n))
    (stdGaussian_map_direction_norm hn)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at h
  simpa [Function.comp_def, Measure.map_apply measurable_norm MeasurableSet.univ] using h

/-- Gaussian direction is independent of Gaussian radius. -/
theorem indepFun_sphereDirection_norm {n : ℕ} (hn : 0 < n) :
    IndepFun (@sphereDirection n) (fun x ↦ ‖x‖) (stdGaussian (Vector n)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (measurable_sphereDirection n).aemeasurable measurable_norm.aemeasurable,
    stdGaussian_map_sphereDirection hn]
  exact stdGaussian_map_direction_norm hn

/-- An independent uniform direction and Gaussian radius reconstruct a Gaussian. -/
theorem sphericalLaw_prod_radius_map_smul {n : ℕ} (hn : 0 < n) :
    ((sphericalLaw n).prod ((stdGaussian (Vector n)).map (fun x ↦ ‖x‖))).map
      (fun p : Vector n × ℝ ↦ p.2 • p.1) = stdGaussian (Vector n) := by
  rw [← stdGaussian_map_direction_norm hn, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def, norm_smul_sphereDirection]

/-- The bridge can transport integrals and integrability, as well as laws. -/
theorem measurePreserving_gaussian_direction_norm {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (fun x : Vector n ↦ (sphereDirection x, ‖x‖))
      (stdGaussian (Vector n))
      ((sphericalLaw n).prod ((stdGaussian (Vector n)).map (fun x ↦ ‖x‖))) :=
  ⟨by fun_prop, stdGaussian_map_direction_norm hn⟩

/-- Normalizing independent Gaussian rows gives exactly the specified row law. -/
theorem gaussianRows_map_sphereDirection (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin m ↦ stdGaussian (Vector n))).map
      (fun A i ↦ sphereDirection (A i)) = sphericalRowsLaw m n := by
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_sphereDirection n).aemeasurable)]
  simp only [stdGaussian_map_sphereDirection hn, sphericalRowsLaw]

/-- A spherical projection times an independent Gaussian radius is a real Gaussian.
This connects the product coupling directly to the scalar Gaussian estimates. -/
theorem sphericalLaw_prod_radius_map_inner {n : ℕ} (hn : 0 < n) (b : Vector n) :
    ((sphericalLaw n).prod ((stdGaussian (Vector n)).map (fun x ↦ ‖x‖))).map
      (fun p : Vector n × ℝ ↦ p.2 * inner ℝ b p.1) =
        gaussianReal 0 (‖b‖ ^ 2).toNNReal := by
  have h := congrArg (Measure.map (fun x ↦ inner ℝ b x))
    (sphericalLaw_prod_radius_map_smul hn)
  rw [Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_inner] at h
  simpa [Function.comp_def, inner_smul_right, real_inner_comm, mul_comm] using h

end NLA.RowDeletion
