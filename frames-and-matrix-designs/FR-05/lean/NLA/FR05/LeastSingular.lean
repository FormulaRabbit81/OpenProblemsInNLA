import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! A finite-dimensional algebraic core for FR-05, Lemma 3.7. -/

namespace NLA.FR05

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The column of the inverse dual to row `i`. -/
noncomputable def inverseRowDual (A : Matrix n n ℝ) (i : n) : n → ℝ :=
  A⁻¹.col i

/-- The Euclidean span of all rows other than `i`. -/
noncomputable def otherRowSpan (A : Matrix n n ℝ) (i : n) :
  Submodule ℝ (EuclideanSpace ℝ n) :=
  Submodule.span ℝ {x | ∃ j : n, j ≠ i ∧ x = WithLp.toLp 2 (A j)}

/-- An inverse column pairs to one with its designated row and to zero with every other row. -/
theorem row_dot_inverseRowDual_eq (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (i j : n) :
    dotProduct (A j) (inverseRowDual A i) = if j = i then 1 else 0 := by
  change (A.mulVec (A⁻¹.col i)) j = _
  rw [← Matrix.mulVec_single_one]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem row_dot_inverseRowDual_ne (A : Matrix n n ℝ) (hA : IsUnit A.det)
    {i j : n} (hji : j ≠ i) :
    dotProduct (A j) (inverseRowDual A i) = 0 := by
  rw [row_dot_inverseRowDual_eq A hA]
  simp [hji]

theorem row_dot_inverseRowDual_self (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (i : n) :
    dotProduct (A i) (inverseRowDual A i) = 1 := by
  rw [row_dot_inverseRowDual_eq A hA]
  simp

/-- The inverse dual vector is orthogonal to the span of the other rows. -/
theorem inverseRowDual_mem_otherRowSpan_orthogonal (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (i : n) :
    WithLp.toLp 2 (inverseRowDual A i) ∈ (otherRowSpan A i)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hspan : otherRowSpan A i ≤ (innerₗ (EuclideanSpace ℝ n)
      (WithLp.toLp 2 (inverseRowDual A i))).ker := by
    rw [otherRowSpan, Submodule.span_le]
    rintro y ⟨j, hji, rfl⟩
    change inner ℝ (WithLp.toLp 2 (inverseRowDual A i)) (WithLp.toLp 2 (A j)) = 0
    rw [real_inner_comm]
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using row_dot_inverseRowDual_ne A hA hji
  change inner ℝ x (WithLp.toLp 2 (inverseRowDual A i)) = 0
  have hker := hspan hx
  change inner ℝ (WithLp.toLp 2 (inverseRowDual A i)) x = 0 at hker
  rw [real_inner_comm] at hker
  exact hker

/-- The Euclidean operator induced by a matrix. -/
noncomputable def euclideanMap (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n :=
  Matrix.toEuclideanLin A

/-- Invertibility of a matrix gives an exact inverse identity on Euclidean coordinate space. -/
theorem inverse_euclideanMap_apply (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (x : EuclideanSpace ℝ n) :
    euclideanMap A⁻¹ (euclideanMap A x) = x := by
  apply WithLp.ofLp_injective
  change A⁻¹.mulVec (A.mulVec (WithLp.ofLp x)) = WithLp.ofLp x
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

/-- Matrix multiplication expands into the inverse matrix's Euclidean columns. -/
theorem euclideanMap_eq_sum_columns (A : Matrix n n ℝ) (y : EuclideanSpace ℝ n) :
    euclideanMap A y = ∑ i, (y i) • WithLp.toLp 2 (A.col i) := by
  apply WithLp.ofLp_injective
  ext j
  simp [euclideanMap, WithLp.ofLp_sum, WithLp.ofLp_smul, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A convenient, exact matrix formulation of a uniform inverse-column bound. -/
def InverseColumnNormBound (A : Matrix n n ℝ) (u : ℝ) : Prop :=
  ∀ i : n, u * ‖WithLp.toLp 2 (A⁻¹.col i)‖ ≤ 1

/-- The row-to-other-rows distance written through the dual inverse column. -/
noncomputable def inverseRowSpanDistance (A : Matrix n n ℝ) (i : n) : ℝ :=
  (‖WithLp.toLp 2 (inverseRowDual A i)‖)⁻¹

/-- Uniformly bounded inverse columns bound the norm of the inverse map.

The factor is the dimension rather than `√n`; this deliberately weaker version is enough
for Li's use of the threshold `n * κ` in Lemma 3.7. -/
theorem inverse_euclideanMap_norm_mul_le_card
    (A : Matrix n n ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hcols : InverseColumnNormBound A u) (y : EuclideanSpace ℝ n) :
    u * ‖euclideanMap A⁻¹ y‖ ≤ (Fintype.card n : ℝ) * ‖y‖ := by
  rw [euclideanMap_eq_sum_columns]
  calc
    u * ‖∑ i, y i • WithLp.toLp 2 (A⁻¹.col i)‖
        ≤ u * ∑ i, ‖y i • WithLp.toLp 2 (A⁻¹.col i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hu
    _ = ∑ i, u * ‖y i • WithLp.toLp 2 (A⁻¹.col i)‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        u * ‖y i • WithLp.toLp 2 (A⁻¹.col i)‖ =
            ‖y i‖ * (u * ‖WithLp.toLp 2 (A⁻¹.col i)‖) := by
          rw [norm_smul]
          ring
        _ ≤ ‖y i‖ * 1 := mul_le_mul_of_nonneg_left (hcols i) (norm_nonneg _)
        _ = ‖y i‖ := mul_one _
    _ ≤ ∑ i, ‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact PiLp.norm_apply_le y i
    _ = (Fintype.card n : ℝ) * ‖y‖ := by simp

/-- `A` has Euclidean least gain at least `s`.  This is a singular-value formulation which
does not require choosing an analytic `sInf` definition of the smallest singular value. -/
def HasEuclideanLowerBound (A : Matrix n n ℝ) (s : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ n, s * ‖x‖ ≤ ‖euclideanMap A x‖

/-- The row-distance proxy supplied by inverse columns yields the deterministic lower singular
bound needed for the Lemma 3.7 union bound. -/
theorem hasEuclideanLowerBound_of_inverseColumnNormBound
    [Nonempty n] (A : Matrix n n ℝ) (hA : IsUnit A.det) {u : ℝ} (hu : 0 ≤ u)
    (hcols : InverseColumnNormBound A u) :
    HasEuclideanLowerBound A (u / (Fintype.card n : ℝ)) := by
  intro x
  have hcard : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbound := inverse_euclideanMap_norm_mul_le_card A hu hcols (euclideanMap A x)
  rw [inverse_euclideanMap_apply A hA x] at hbound
  calc
    (u / (Fintype.card n : ℝ)) * ‖x‖ = (u * ‖x‖) / (Fintype.card n : ℝ) := by
      ring
    _ ≤ ‖euclideanMap A x‖ := (div_le_iff₀ hcard).2 (by
      simpa [mul_comm] using hbound)

/-- The span of the other rows is exactly the kernel of the dual inverse-column functional.
This is the finite-dimensional row-to-span bridge in Lemma 3.7. -/
theorem otherRowSpan_eq_inverseRowDual_ker (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (i : n) :
    otherRowSpan A i = (innerₗ (EuclideanSpace ℝ n)
      (WithLp.toLp 2 (inverseRowDual A i))).ker := by
  apply le_antisymm
  · rw [otherRowSpan, Submodule.span_le]
    rintro y ⟨j, hji, rfl⟩
    change inner ℝ (WithLp.toLp 2 (inverseRowDual A i)) (WithLp.toLp 2 (A j)) = 0
    rw [real_inner_comm]
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using row_dot_inverseRowDual_ne A hA hji
  · intro x hx
    change inner ℝ (WithLp.toLp 2 (inverseRowDual A i)) x = 0 at hx
    rw [real_inner_comm] at hx
    have hcoefi : (Matrix.vecMul (WithLp.ofLp x) A⁻¹) i = 0 := by
      change dotProduct (WithLp.ofLp x) (A⁻¹.col i) = 0
      simpa [PiLp.inner_apply, dotProduct, inverseRowDual, mul_comm] using hx
    have hsum : ∑ j, (Matrix.vecMul (WithLp.ofLp x) A⁻¹) j • WithLp.toLp 2 (A j) ∈
        otherRowSpan A i := by
      rw [otherRowSpan]
      apply Submodule.sum_mem
      intro j _
      by_cases hji : j = i
      · subst j
        rw [hcoefi]
        simp
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩)
    rw [← WithLp.toLp_ofLp 2 x]
    have hv : WithLp.ofLp x =
        Matrix.vecMul (Matrix.vecMul (WithLp.ofLp x) A⁻¹) A := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hA, Matrix.vecMul_one]
    rw [hv, Matrix.vecMul_eq_sum]
    simpa using hsum

/-- A pointwise, infimum-free formulation of the distance from a vector to a subspace. -/
def IsExactSubspaceDistance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (r : E) (d : ℝ) : Prop :=
  (∃ z : E, z ∈ S ∧ ‖r - z‖ = d) ∧ ∀ z : E, z ∈ S → d ≤ ‖r - z‖

/-- The source's row-distance bad event, expressed without choosing an `sInf` definition. -/
noncomputable def RowSpanDistanceBad (A : Matrix n n ℝ) (i : n) (t : ℝ) : Prop :=
  ∃ d : ℝ, IsExactSubspaceDistance (otherRowSpan A i) (WithLp.toLp 2 (A i)) d ∧ d < t

/-- The inverse-column normal gives the exact row-to-other-rows distance.

This avoids any choice of a `sInf`-based singular-value definition while retaining the full
metric content used in Li's Lemma 3.7. -/
theorem inverseRowDual_gives_exact_rowSpan_distance (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (i : n) :
    IsExactSubspaceDistance (otherRowSpan A i) (WithLp.toLp 2 (A i))
      (inverseRowSpanDistance A i) := by
  let w : EuclideanSpace ℝ n := WithLp.toLp 2 (inverseRowDual A i)
  let r : EuclideanSpace ℝ n := WithLp.toLp 2 (A i)
  have hdual_ne : inverseRowDual A i ≠ 0 := by
    intro hzero
    have hself := row_dot_inverseRowDual_self A hA i
    rw [hzero] at hself
    norm_num at hself
  have hw_ne : w ≠ 0 := by
    intro hzero
    apply hdual_ne
    simpa [w] using hzero
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  have hrow : inner ℝ w r = 1 := by
    simpa [w, r, PiLp.inner_apply, dotProduct, mul_comm] using
      row_dot_inverseRowDual_self A hA i
  let q : EuclideanSpace ℝ n := (‖w‖ ^ 2)⁻¹ • w
  have hq_inner : inner ℝ w q = 1 := by
    dsimp [q]
    rw [inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp
  have hq_norm : ‖q‖ = ‖w‖⁻¹ := by
    dsimp [q]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    field_simp
  have hz_mem : r - q ∈ otherRowSpan A i := by
    rw [otherRowSpan_eq_inverseRowDual_ker A hA i]
    change inner ℝ w (r - q) = 0
    rw [inner_sub_right, hrow, hq_inner]
    norm_num
  constructor
  · refine ⟨r - q, hz_mem, ?_⟩
    change ‖r - (r - q)‖ = ‖w‖⁻¹
    rw [show r - (r - q) = q by abel, hq_norm]
  · intro z hz
    have hz_orth : inner ℝ w z = 0 := by
      rw [otherRowSpan_eq_inverseRowDual_ker A hA i] at hz
      exact hz
    have hinner : inner ℝ w (r - z) = 1 := by
      rw [inner_sub_right, hrow, hz_orth]
      norm_num
    have hcs := abs_real_inner_le_norm w (r - z)
    rw [hinner, abs_one] at hcs
    calc
      ‖w‖⁻¹ = 1 / ‖w‖ := by rw [one_div]
      _ ≤ ‖r - z‖ := (div_le_iff₀ hw_pos).2 (by simpa [mul_comm] using hcs)

theorem inverseRowDual_norm_pos (A : Matrix n n ℝ) (hA : IsUnit A.det) (i : n) :
    0 < ‖WithLp.toLp 2 (inverseRowDual A i)‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hself := row_dot_inverseRowDual_self A hA i
  have hdual : inverseRowDual A i = 0 := by
    simpa using hzero
  rw [hdual] at hself
  norm_num at hself

/-- A lower bound on every exact row-span distance gives the inverse-column condition. -/
theorem inverseColumnNormBound_of_le_inverseRowSpanDistance
    (A : Matrix n n ℝ) (hA : IsUnit A.det) {u : ℝ}
    (hgap : ∀ i : n, u ≤ inverseRowSpanDistance A i) :
    InverseColumnNormBound A u := by
  intro i
  have hpos := inverseRowDual_norm_pos A hA i
  calc
    u * ‖WithLp.toLp 2 (A⁻¹.col i)‖ ≤
        (‖WithLp.toLp 2 (A⁻¹.col i)‖)⁻¹ * ‖WithLp.toLp 2 (A⁻¹.col i)‖ :=
      mul_le_mul_of_nonneg_right (by simpa [inverseRowSpanDistance, inverseRowDual] using hgap i)
        (norm_nonneg _)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

/-- The deterministic core of Li's Lemma 3.7: if every row is at distance at least
`n * κ` from the span of the other rows, then the Euclidean least gain is at least `κ`. -/
theorem hasEuclideanLowerBound_of_rowSpanDistanceBound
    [Nonempty n] (A : Matrix n n ℝ) (hA : IsUnit A.det) {κ : ℝ} (hκ : 0 ≤ κ)
    (hgap : ∀ i : n, (Fintype.card n : ℝ) * κ ≤ inverseRowSpanDistance A i) :
    HasEuclideanLowerBound A κ := by
  have hcard : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbound := hasEuclideanLowerBound_of_inverseColumnNormBound A hA
    (mul_nonneg hcard.le hκ)
    (inverseColumnNormBound_of_le_inverseRowSpanDistance A hA hgap)
  have heq : ((Fintype.card n : ℝ) * κ) / (Fintype.card n : ℝ) = κ := by
    field_simp
  rw [heq] at hbound
  exact hbound

/-- Contrapositive form used before applying a union bound to the row events. -/
theorem not_hasEuclideanLowerBound_implies_not_all_rowSpanDistances
    [Nonempty n] (A : Matrix n n ℝ) (hA : IsUnit A.det) {κ : ℝ} (hκ : 0 ≤ κ) :
    ¬ HasEuclideanLowerBound A κ →
      ¬ (∀ i : n, (Fintype.card n : ℝ) * κ ≤ inverseRowSpanDistance A i) := by
  intro hnot hall
  exact hnot (hasEuclideanLowerBound_of_rowSpanDistanceBound A hA hκ hall)

/-- A singular matrix has a row in the span of its other rows. -/
theorem exists_row_mem_otherRowSpan_of_not_isUnit_det (A : Matrix n n ℝ)
    (hA : ¬ IsUnit A.det) :
    ∃ i : n, WithLp.toLp 2 (A i) ∈ otherRowSpan A i := by
  have hnot_unit : ¬ IsUnit A := by
    intro hunit
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have hdep : ¬ LinearIndependent ℝ A.row := by
    intro hli
    exact hnot_unit ((Matrix.linearIndependent_rows_iff_isUnit).mp hli)
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  rcases hdep with ⟨g, hsum, i, hgi⟩
  have hsumE : ∑ j, g j • WithLp.toLp 2 (A j) = 0 := by
    apply WithLp.ofLp_injective
    simpa [WithLp.ofLp_sum, WithLp.ofLp_smul, Matrix.row] using hsum
  have hsum_other : ∑ j ∈ Finset.univ.erase i, g j • WithLp.toLp 2 (A j) ∈
      otherRowSpan A i := by
    apply Submodule.sum_mem
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩)
  have hsplit : (∑ j ∈ Finset.univ.erase i, g j • WithLp.toLp 2 (A j)) +
      g i • WithLp.toLp 2 (A i) = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsumE
  have hscalar : g i • WithLp.toLp 2 (A i) ∈ otherRowSpan A i := by
    rw [eq_neg_of_add_eq_zero_right hsplit]
    exact (otherRowSpan A i).neg_mem hsum_other
  exact ⟨i, ((otherRowSpan A i).smul_mem_iff hgi).mp hscalar⟩

/-- In the singular case, one row has zero distance to the span of the other rows. -/
theorem exists_zero_exact_rowSpan_distance_of_not_isUnit_det (A : Matrix n n ℝ)
    (hA : ¬ IsUnit A.det) :
    ∃ i : n, IsExactSubspaceDistance (otherRowSpan A i) (WithLp.toLp 2 (A i)) 0 := by
  rcases exists_row_mem_otherRowSpan_of_not_isUnit_det A hA with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  constructor
  · exact ⟨WithLp.toLp 2 (A i), hi, by simp⟩
  · intro z _
    exact norm_nonneg _

/-- The full deterministic event inclusion behind the Lemma 3.7 union bound. -/
theorem exists_inverseRowSpanDistance_lt_card_mul_of_not_hasEuclideanLowerBound
    [Nonempty n] (A : Matrix n n ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hnot : ¬ HasEuclideanLowerBound A κ) :
    ∃ i : n, inverseRowSpanDistance A i < (Fintype.card n : ℝ) * κ := by
  by_cases hunit : IsUnit A.det
  · have hnotall :=
      not_hasEuclideanLowerBound_implies_not_all_rowSpanDistances A hunit hκ.le hnot
    push Not at hnotall
    exact hnotall
  · rcases exists_zero_exact_rowSpan_distance_of_not_isUnit_det A hunit with ⟨i, _⟩
    refine ⟨i, ?_⟩
    have hcard : 0 < (Fintype.card n : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [inverseRowSpanDistance, inverseRowDual,
      Matrix.nonsing_inv_apply_not_isUnit A hunit]
    change ‖WithLp.toLp 2 (0 : n → ℝ)‖⁻¹ < _
    simpa using mul_pos hcard hκ

/-- The full deterministic row-distance event inclusion behind Lemma 3.7. -/
theorem exists_rowSpanDistanceBad_of_not_hasEuclideanLowerBound
    [Nonempty n] (A : Matrix n n ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hnot : ¬ HasEuclideanLowerBound A κ) :
    ∃ i : n, RowSpanDistanceBad A i ((Fintype.card n : ℝ) * κ) := by
  by_cases hunit : IsUnit A.det
  · have hnotall :=
      not_hasEuclideanLowerBound_implies_not_all_rowSpanDistances A hunit hκ.le hnot
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    exact ⟨i, inverseRowSpanDistance A i,
      inverseRowDual_gives_exact_rowSpan_distance A hunit i, hi⟩
  · rcases exists_zero_exact_rowSpan_distance_of_not_isUnit_det A hunit with ⟨i, hzero⟩
    refine ⟨i, 0, hzero, ?_⟩
    have hcard : 0 < (Fintype.card n : ℝ) := by
      exact_mod_cast Fintype.card_pos
    exact mul_pos hcard hκ

/-- A finite-row union-bound wrapper for the deterministic Lemma 3.7 inclusion. -/
theorem measureReal_not_hasEuclideanLowerBound_le_sum_rowEvents
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [Nonempty n] (J : Ω → Matrix n n ℝ) {κ : ℝ} (hκ : 0 < κ) :
    μ.real {ω | ¬ HasEuclideanLowerBound (J ω) κ} ≤
      ∑ i, μ.real {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} := by
  have hsubset : {ω | ¬ HasEuclideanLowerBound (J ω) κ} ⊆
      ⋃ i ∈ (Finset.univ : Finset n),
        {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} := by
    intro ω hω
    obtain ⟨i, hi⟩ :=
      exists_rowSpanDistanceBad_of_not_hasEuclideanLowerBound (J ω) hκ hω
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, hi⟩⟩
  calc
    μ.real {ω | ¬ HasEuclideanLowerBound (J ω) κ} ≤
        μ.real (⋃ i ∈ (Finset.univ : Finset n),
          {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)}) :=
      measureReal_mono hsubset (measure_lt_top μ _).ne
    _ ≤ ∑ i ∈ (Finset.univ : Finset n),
        μ.real {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ i, μ.real {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} := by
      simp

/-- A uniform per-row small-ball estimate upgrades to the usual cardinality-times-probability
union bound for the least-gain failure event. -/
theorem measureReal_not_hasEuclideanLowerBound_le_card_mul_of_rowEvent_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [Nonempty n] (J : Ω → Matrix n n ℝ) {κ p : ℝ} (hκ : 0 < κ)
    (hrow : ∀ i : n,
      μ.real {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} ≤ p) :
    μ.real {ω | ¬ HasEuclideanLowerBound (J ω) κ} ≤ (Fintype.card n : ℝ) * p := by
  calc
    μ.real {ω | ¬ HasEuclideanLowerBound (J ω) κ} ≤
        ∑ i, μ.real {ω | RowSpanDistanceBad (J ω) i ((Fintype.card n : ℝ) * κ)} :=
      measureReal_not_hasEuclideanLowerBound_le_sum_rowEvents μ J hκ
    _ ≤ ∑ _i : n, p := by
      apply Finset.sum_le_sum
      intro i _
      exact hrow i
    _ = (Fintype.card n : ℝ) * p := by simp

end FR05
