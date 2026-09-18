/-
Conservative finite-dimensional norm bounds for the polynomial factor chart.

This temporary development uses the sup norm on finite coordinate functions.
It isolates the finite-dimensional algebra needed to turn the exact
derivative-variation identity into a quantitative estimate.
-/
import NLA.FR05.DerivativeControl
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

namespace NLA.FR05

/-- A finite-dimensional dot-product estimate using the ambient sup norm on
coordinate functions. -/
theorem norm_star_dotProduct_le {d : ℕ} (a b : Signal d) :
    ‖star a ⬝ᵥ b‖ ≤ (d : ℝ) * ‖a‖ * ‖b‖ := by
  have hsum (x : Signal d) :
      ∑ i, ‖x i‖ ≤ (d : ℝ) * ‖x‖ := by
    simpa [Fintype.card_fin, nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm x)
  calc
    ‖star a ⬝ᵥ b‖ ≤ ∑ i, ‖(star a) i * b i‖ := by
      simpa only [dotProduct] using
        (norm_sum_le Finset.univ (fun i => (star a) i * b i))
    _ = ∑ i, ‖a i‖ * ‖b i‖ := by
      simp [Pi.star_apply]
    _ ≤ ∑ i, ‖a i‖ * ‖b‖ := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (norm_le_pi_norm b i)
        (norm_nonneg (a i))
    _ = (∑ i, ‖a i‖) * ‖b‖ := by
      rw [Finset.sum_mul]
    _ ≤ ((d : ℝ) * ‖a‖) * ‖b‖ := by
      exact mul_le_mul_of_nonneg_right (hsum a) (norm_nonneg _)

/-- Evaluation of a rank-one matrix on a vector, in the convention used by
`quadraticForm`. -/
theorem quadraticForm_vecMulVec_cross_norm {d : ℕ} (a u v : Signal d) :
    quadraticForm (Matrix.vecMulVec u (star v)) a =
      (star a ⬝ᵥ u) * (star v ⬝ᵥ a) := by
  rw [quadraticForm, Matrix.vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul, Matrix.star_dotProduct]
  ring

/-- A rank-one quadratic-form bound.  The factor `d² ‖a‖²` is the explicit
row energy created by evaluating both linear factors against `a`. -/
theorem norm_quadraticForm_vecMulVec_cross_le {d : ℕ}
    (a u v : Signal d) :
    ‖quadraticForm (Matrix.vecMulVec u (star v)) a‖ ≤
      (d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖u‖ * ‖v‖ := by
  rw [quadraticForm_vecMulVec_cross_norm, norm_mul]
  calc
    ‖star a ⬝ᵥ u‖ * ‖star v ⬝ᵥ a‖ ≤
        ((d : ℝ) * ‖a‖ * ‖u‖) * ((d : ℝ) * ‖v‖ * ‖a‖) := by
      exact mul_le_mul (norm_star_dotProduct_le a u)
        (norm_star_dotProduct_le v a) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _))
    _ = (d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖u‖ * ‖v‖ := by ring

/-- A conservative norm bound for the symmetric difference of two rank-one
cross terms.  This is the finite-dimensional pattern occurring in the
derivative variation of the polynomial factor chart. -/
theorem norm_quadraticForm_cross_sym_difference_le {d : ℕ}
    (a u v x y : Signal d) :
    ‖quadraticForm
      (Matrix.vecMulVec u (star v) + Matrix.vecMulVec v (star u) -
        Matrix.vecMulVec x (star y) - Matrix.vecMulVec y (star x)) a‖ ≤
      2 * (d : ℝ) ^ 2 * ‖a‖ ^ 2 * (‖u‖ * ‖v‖ + ‖x‖ * ‖y‖) := by
  rw [quadraticForm_sub, quadraticForm_sub, quadraticForm_add]
  calc
    ‖quadraticForm (Matrix.vecMulVec u (star v)) a +
        quadraticForm (Matrix.vecMulVec v (star u)) a -
          quadraticForm (Matrix.vecMulVec x (star y)) a -
            quadraticForm (Matrix.vecMulVec y (star x)) a‖ ≤
        ‖quadraticForm (Matrix.vecMulVec u (star v)) a‖ +
          ‖quadraticForm (Matrix.vecMulVec v (star u)) a‖ +
            ‖quadraticForm (Matrix.vecMulVec x (star y)) a‖ +
              ‖quadraticForm (Matrix.vecMulVec y (star x)) a‖ := by
      calc
        _ ≤ ‖quadraticForm (Matrix.vecMulVec u (star v)) a +
            quadraticForm (Matrix.vecMulVec v (star u)) a -
              quadraticForm (Matrix.vecMulVec x (star y)) a‖ +
                ‖quadraticForm (Matrix.vecMulVec y (star x)) a‖ :=
          norm_sub_le _ _
        _ ≤ (‖quadraticForm (Matrix.vecMulVec u (star v)) a +
            quadraticForm (Matrix.vecMulVec v (star u)) a‖ +
              ‖quadraticForm (Matrix.vecMulVec x (star y)) a‖) +
                ‖quadraticForm (Matrix.vecMulVec y (star x)) a‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖quadraticForm (Matrix.vecMulVec u (star v)) a‖ +
            ‖quadraticForm (Matrix.vecMulVec v (star u)) a‖) +
              ‖quadraticForm (Matrix.vecMulVec x (star y)) a‖) +
                ‖quadraticForm (Matrix.vecMulVec y (star x)) a‖ := by
          gcongr
          exact norm_add_le _ _
        _ = ‖quadraticForm (Matrix.vecMulVec u (star v)) a‖ +
          ‖quadraticForm (Matrix.vecMulVec v (star u)) a‖ +
            ‖quadraticForm (Matrix.vecMulVec x (star y)) a‖ +
              ‖quadraticForm (Matrix.vecMulVec y (star x)) a‖ := by ring
    _ ≤ ((d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖u‖ * ‖v‖) +
          ((d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖v‖ * ‖u‖) +
            ((d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖x‖ * ‖y‖) +
              ((d : ℝ) ^ 2 * ‖a‖ ^ 2 * ‖y‖ * ‖x‖) := by
      gcongr
      · exact norm_quadraticForm_vecMulVec_cross_le a u v
      · exact norm_quadraticForm_vecMulVec_cross_le a v u
      · exact norm_quadraticForm_vecMulVec_cross_le a x y
      · exact norm_quadraticForm_vecMulVec_cross_le a y x
    _ = 2 * (d : ℝ) ^ 2 * ‖a‖ ^ 2 * (‖u‖ * ‖v‖ + ‖x‖ * ‖y‖) := by ring

/-- The explicit squared Euclidean energy is nonnegative. -/
theorem squaredEuclideanNorm_nonneg {d : ℕ} (a : Signal d) :
    0 ≤ squaredEuclideanNorm a := by
  unfold squaredEuclideanNorm
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (a i)

/-- Lean's ambient finite-function norm is a coordinate sup norm; it is
controlled by the explicit Euclidean energy that appears in the source's
event (3.22). -/
theorem norm_sq_le_squaredEuclideanNorm {d : ℕ} (a : Signal d) :
    ‖a‖ ^ 2 ≤ squaredEuclideanNorm a := by
  have henergy : 0 ≤ squaredEuclideanNorm a := squaredEuclideanNorm_nonneg a
  have hnorm : ‖a‖ ≤ Real.sqrt (squaredEuclideanNorm a) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    calc
      ‖a i‖ ^ 2 = Complex.normSq (a i) := Complex.sq_norm _
      _ ≤ ∑ j, Complex.normSq (a j) :=
        Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (a j))
          (Finset.mem_univ i)
      _ = (Real.sqrt (squaredEuclideanNorm a)) ^ 2 :=
        (Real.sq_sqrt henergy).symm
  calc
    ‖a‖ ^ 2 ≤ (Real.sqrt (squaredEuclideanNorm a)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnorm
    _ = squaredEuclideanNorm a := Real.sq_sqrt henergy

/-- The deterministic row energy used by the conservative sup-coordinate
bound.  For the source law, the tail estimates control this quantity on the
good event; the factor `(n + 2)²` is a deliberately non-sharp dimensional
loss. -/
def plantedRowSupEnergy {n : ℕ} (row : PlantedRow n) : ℝ :=
  ((n + 2 : ℕ) : ℝ) ^ 2 * ‖plantedColumn row‖ ^ 2 / row.radial

/-- The same conservative row energy with Lean's sup norm replaced by the
explicit Euclidean energy used in the source's tail event (3.22). -/
def plantedRowEuclideanEnergy {n : ℕ} (row : PlantedRow n) : ℝ :=
  ((n + 2 : ℕ) : ℝ) ^ 2 * squaredEuclideanNorm (plantedColumn row) /
    row.radial

theorem plantedRowSupEnergy_le_euclideanEnergy {n : ℕ} (row : PlantedRow n) :
    plantedRowSupEnergy row ≤ plantedRowEuclideanEnergy row := by
  unfold plantedRowSupEnergy plantedRowEuclideanEnergy
  apply div_le_div_of_nonneg_right _ row.radial_pos.le
  exact mul_le_mul_of_nonneg_left (norm_sq_le_squaredEuclideanNorm _)
    (sq_nonneg _)

/-- The Euclidean-energy row constant is expressed solely through the radial
variable and the Gaussian tail energy, exactly the quantities controlled in
the source's event (3.22). -/
theorem plantedRowEuclideanEnergy_eq_radial_tail {n : ℕ} (row : PlantedRow n) :
    plantedRowEuclideanEnergy row =
      ((n + 2 : ℕ) : ℝ) ^ 2 *
        (row.radial + squaredEuclideanNorm row.tail) / row.radial := by
  unfold plantedRowEuclideanEnergy
  rw [squaredEuclideanNorm_plantedColumn]

theorem plantedRowSupEnergy_nonneg {n : ℕ} (row : PlantedRow n) :
    0 ≤ plantedRowSupEnergy row := by
  unfold plantedRowSupEnergy
  exact div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) row.radial_pos.le

/-- The block norm used for factor-chart directions: each signal component
uses its finite-coordinate sup norm.  It is a conservative replacement for
the Euclidean chart norm in the source's local Lipschitz argument. -/
def factorDirectionSup {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  ‖plusDirection s b z‖ + ‖minusDirection s t‖

theorem factorDirectionSup_nonneg {n : ℕ} (s : ℝ) (b : ℂ)
    (z t : Signal n) : 0 ≤ factorDirectionSup s b z t := by
  unfold factorDirectionSup
  exact add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem factorCross_le_factorDirectionSup_mul {n : ℕ}
    (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    ‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
        ‖minusDirection σ q‖ * ‖minusDirection s t‖ ≤
      factorDirectionSup s b z t * factorDirectionSup σ c p q := by
  unfold factorDirectionSup
  nlinarith [
    mul_nonneg (norm_nonneg (plusDirection s b z))
      (norm_nonneg (minusDirection σ q)),
    mul_nonneg (norm_nonneg (minusDirection s t))
      (norm_nonneg (plusDirection σ c p))]

/-- Norm control of the bilinear derivative variation before its real-part
normalization. -/
theorem norm_quadraticForm_factorChartDerivativeVariation_le {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    ‖quadraticForm (factorChartDerivativeVariation s b z t σ c p q)
      (plantedColumn row)‖ ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 * ‖plantedColumn row‖ ^ 2 *
        (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
          ‖minusDirection σ q‖ * ‖minusDirection s t‖) := by
  simpa [factorChartDerivativeVariation] using
    (norm_quadraticForm_cross_sym_difference_le (plantedColumn row)
      (plusDirection σ c p) (plusDirection s b z)
      (minusDirection σ q) (minusDirection s t))

/-- A source-specific, conservative Jacobian-variation bound in the
sup-coordinate norm.  It is an exact deterministic estimate for the
polynomial factor chart; probabilistic control of `plantedRowSupEnergy` is
the remaining source-law input. -/
theorem abs_plantedEquationDerivativeVariation_le {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    |plantedEquationDerivativeVariation row s b z t σ c p q| ≤
      2 * plantedRowSupEnergy row *
        (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
          ‖minusDirection σ q‖ * ‖minusDirection s t‖) := by
  unfold plantedEquationDerivativeVariation
  rw [abs_div, abs_of_pos row.radial_pos]
  have hnorm := norm_quadraticForm_factorChartDerivativeVariation_le
    row s σ b c z t p q
  have hre :
      |(quadraticForm (factorChartDerivativeVariation s b z t σ c p q)
        (plantedColumn row)).re| ≤
        2 * ((n + 2 : ℕ) : ℝ) ^ 2 * ‖plantedColumn row‖ ^ 2 *
          (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
            ‖minusDirection σ q‖ * ‖minusDirection s t‖) :=
    (Complex.abs_re_le_norm _).trans hnorm
  calc
    |(quadraticForm (factorChartDerivativeVariation s b z t σ c p q)
        (plantedColumn row)).re| / row.radial ≤
        (2 * ((n + 2 : ℕ) : ℝ) ^ 2 * ‖plantedColumn row‖ ^ 2 *
          (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
            ‖minusDirection σ q‖ * ‖minusDirection s t‖)) / row.radial :=
      div_le_div_of_nonneg_right hre row.radial_pos.le
    _ = 2 * plantedRowSupEnergy row *
        (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
          ‖minusDirection σ q‖ * ‖minusDirection s t‖) := by
      unfold plantedRowSupEnergy
      field_simp [row.radial_pos.ne']

/-- The rowwise Jacobian variation is bilinear in the base point and
direction for a concrete sup-coordinate chart norm. -/
theorem abs_plantedEquationDerivativeVariation_le_sup {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    |plantedEquationDerivativeVariation row s b z t σ c p q| ≤
      2 * plantedRowSupEnergy row *
        factorDirectionSup s b z t * factorDirectionSup σ c p q := by
  calc
    |plantedEquationDerivativeVariation row s b z t σ c p q| ≤
        2 * plantedRowSupEnergy row *
          (‖plusDirection σ c p‖ * ‖plusDirection s b z‖ +
            ‖minusDirection σ q‖ * ‖minusDirection s t‖) :=
      abs_plantedEquationDerivativeVariation_le row s σ b c z t p q
    _ ≤ 2 * plantedRowSupEnergy row *
          (factorDirectionSup s b z t * factorDirectionSup σ c p q) := by
      exact mul_le_mul_of_nonneg_left
        (factorCross_le_factorDirectionSup_mul s σ b c z t p q)
        (mul_nonneg (by norm_num) (plantedRowSupEnergy_nonneg row))
    _ = 2 * plantedRowSupEnergy row *
          factorDirectionSup s b z t * factorDirectionSup σ c p q := by ring

/-- The same bound written as a difference from the checked seed Jacobian.
This is the direct polynomial-chart analogue of the derivative-variation
input to the source's estimate (3.23). -/
theorem abs_plantedEquationDirectional_sub_linear_le_sup {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    |plantedEquationDirectional row s b z t σ c p q -
        plantedEquationLinear row σ c p q| ≤
      2 * plantedRowSupEnergy row *
        factorDirectionSup s b z t * factorDirectionSup σ c p q := by
  rw [plantedEquationDirectional_eq_linear_add_variation]
  have hcancel :
      plantedEquationLinear row σ c p q +
          plantedEquationDerivativeVariation row s b z t σ c p q -
            plantedEquationLinear row σ c p q =
        plantedEquationDerivativeVariation row s b z t σ c p q := by
    ring
  rw [hcancel]
  exact abs_plantedEquationDerivativeVariation_le_sup row s σ b c z t p q

/-- Ball-form corollary of the rowwise derivative-variation bound.  In a
later source-parameter instantiation, one may set `R = ε = M⁻⁵⁰`; all
dependence on the row realization is isolated in `plantedRowSupEnergy`. -/
theorem abs_plantedEquationDirectional_sub_linear_le_of_sup_le {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n)
    {R S : ℝ} (hR : 0 ≤ R)
    (hbase : factorDirectionSup s b z t ≤ R)
    (hdirection : factorDirectionSup σ c p q ≤ S) :
    |plantedEquationDirectional row s b z t σ c p q -
        plantedEquationLinear row σ c p q| ≤
      2 * plantedRowSupEnergy row * R * S := by
  calc
    |plantedEquationDirectional row s b z t σ c p q -
        plantedEquationLinear row σ c p q| ≤
        2 * plantedRowSupEnergy row * factorDirectionSup s b z t *
          factorDirectionSup σ c p q :=
      abs_plantedEquationDirectional_sub_linear_le_sup row s σ b c z t p q
    _ ≤ 2 * plantedRowSupEnergy row * (R * S) := by
      calc
        2 * plantedRowSupEnergy row * factorDirectionSup s b z t *
            factorDirectionSup σ c p q =
          (2 * plantedRowSupEnergy row) *
            (factorDirectionSup s b z t * factorDirectionSup σ c p q) := by ring
        _ ≤ (2 * plantedRowSupEnergy row) * (R * S) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul hbase hdirection
              (factorDirectionSup_nonneg σ c p q) hR
          · exact mul_nonneg (by norm_num) (plantedRowSupEnergy_nonneg row)
    _ = 2 * plantedRowSupEnergy row * R * S := by ring

end NLA.FR05
