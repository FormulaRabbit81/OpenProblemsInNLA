/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.NumericData
import NLA.IE17.Geometry
import LeanCert.Tactic

noncomputable section
open Matrix
open scoped InnerProductSpace
namespace NLA.IE17

private theorem normalResidual_difference {m n : ℕ} (A : Mat m n) (b : Vec m)
    (x y : Vec n) :
    normalResidual A b y = normalResidual A b x -
      (A.transpose * A).toEuclideanLin (y - x) := by
  simp only [normalResidual, residual, map_sub, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  abel

/-- Orthogonality is imposed on the entire real Krylov subspace. Its Pythagorean
identity proves global normal-residual minimization; injectivity makes that
minimizer unique, and hence also minimum length. -/
theorem isLSMR_of_normal_orthogonality {m n k : ℕ} {A : Mat m n} {b : Vec m}
    {x : Vec n}
    (hH : Function.Injective (A.transpose * A).toEuclideanLin)
    (hx : x ∈ krylov A b k)
    (ho : ∀ y ∈ krylov A b k,
      ⟪normalResidual A b x, (A.transpose * A).toEuclideanLin y⟫_ℝ = 0) :
    IsLSMRIterate A b k x := by
  have hp (y : Vec n) (hy : y ∈ krylov A b k) :
      ‖normalResidual A b y‖ ^ 2 = ‖normalResidual A b x‖ ^ 2 +
        ‖(A.transpose * A).toEuclideanLin (y - x)‖ ^ 2 := by
    rw [normalResidual_difference A b x y, norm_sub_sq_real]
    rw [ho (y - x) ((krylov A b k).sub_mem hy hx)]
    ring
  refine ⟨hx, ?_, ?_⟩
  · intro y hy
    have h := hp y hy
    nlinarith [sq_nonneg ‖(A.transpose * A).toEuclideanLin (y - x)‖,
      norm_nonneg (normalResidual A b x), norm_nonneg (normalResidual A b y)]
  · intro y hy heq
    have hs : ‖(A.transpose * A).toEuclideanLin (y - x)‖ ^ 2 = 0 := by
      have hpy := hp y hy
      rw [heq] at hpy
      linarith
    have hz : (A.transpose * A).toEuclideanLin (y - x) = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    have hyx : y = x := by
      apply hH
      simpa only [map_sub, sub_eq_zero] using hz
    simp [hyx]

/-- Extending orthogonality from generators to the full real span. -/
theorem normal_orthogonality_of_generators {m n k : ℕ} {A : Mat m n} {b : Vec m}
    {x : Vec n}
    (hg : ∀ j : ℕ, j < k →
      ⟪normalResidual A b x,
        (A.transpose * A).toEuclideanLin
          (((A.transpose * A) ^ j).toEuclideanLin (A.transpose.toEuclideanLin b))⟫_ℝ = 0) :
    ∀ y ∈ krylov A b k,
      ⟪normalResidual A b x, (A.transpose * A).toEuclideanLin y⟫_ℝ = 0 := by
  intro y hy
  change y ∈ Submodule.span ℝ _ at hy
  induction hy using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j, hj, rfl⟩ := hv
      exact hg j hj
  | zero => simp
  | add u v hu hv ihu ihv => simp only [map_add, inner_add_right, ihu, ihv, zero_add]
  | smul a v hv ih => simp only [map_smul, inner_smul_right, ih, mul_zero]

theorem witnessA_injective : Function.Injective witnessA.toEuclideanLin := by
  intro x y h
  have hc (i : Fin 4) := congrArg (fun z : Vec 4 => z i) h
  ext i
  fin_cases i
  · simpa [euclidean_apply_coord, witnessA, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] using hc 0
  · change x 1 = y 1
    have hh := hc 1
    norm_num [euclidean_apply_coord, witnessA, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] at hh
    linarith
  · change x 2 = y 2
    have hh := hc 2
    norm_num [euclidean_apply_coord, witnessA, Fin.sum_univ_three,
      Matrix.cons_val_two] at hh
    linarith

private theorem witness_gram : witnessA.transpose * witnessA =
    !![(1 : ℝ), 0, 0; 0, 36, 0; 0, 0, 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem witnessH_injective :
    Function.Injective (witnessA.transpose * witnessA).toEuclideanLin := by
  intro x y h
  rw [witness_gram] at h
  have hc (i : Fin 3) := congrArg (fun z : Vec 3 => z i) h
  ext i
  fin_cases i
  · simpa [euclidean_apply_coord, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] using hc 0
  · change x 1 = y 1
    have hh := hc 1
    norm_num [euclidean_apply_coord, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] at hh
    linarith
  · change x 2 = y 2
    have hh := hc 2
    norm_num [euclidean_apply_coord, Fin.sum_univ_three, Matrix.cons_val_two] at hh
    linarith

private def witnessGenerator (j : ℕ) : Vec 3 :=
  ((witnessA.transpose * witnessA) ^ j).toEuclideanLin
    (witnessA.transpose.toEuclideanLin witnessB)

private theorem witness_rhs_normal :
    witnessA.transpose.toEuclideanLin witnessB = WithLp.toLp 2 ![(11 : ℝ),6,5] := by
  ext i
  change (∑ j : Fin 4, witnessA j i * witnessB j) = ![(11 : ℝ),6,5] i
  fin_cases i <;>
    norm_num [witnessA, witnessB, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem generator_zero : witnessGenerator 0 = WithLp.toLp 2 ![(11 : ℝ),6,5] := by
  unfold witnessGenerator
  rw [pow_zero]
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] using
    witness_rhs_normal

private theorem generator_one : witnessGenerator 1 = WithLp.toLp 2 ![(11 : ℝ),216,125] := by
  unfold witnessGenerator
  rw [pow_one, witness_gram, witness_rhs_normal]
  ext i
  fin_cases i <;>
    norm_num [euclidean_apply_coord, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem generator_two : witnessGenerator 2 = WithLp.toLp 2 ![(11 : ℝ),7776,3125] := by
  unfold witnessGenerator
  rw [witness_gram, witness_rhs_normal, pow_two]
  ext i
  simp only [euclidean_apply_coord, Matrix.mul_apply]
  fin_cases i <;>
    norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem generator_mem {j k : ℕ} (hj : j < k) :
    witnessGenerator j ∈ krylov witnessA witnessB k :=
  Submodule.subset_span ⟨j, hj, rfl⟩

theorem witness_normalResidual_zero : normalResidual witnessA witnessB 0 =
    WithLp.toLp 2 ![(11 : ℝ), 6, 5] := by
  simpa only [normalResidual, residual, map_zero, sub_zero] using witness_rhs_normal

theorem witness_normalResidual_one : normalResidual witnessA witnessB witnessX₁ =
    WithLp.toLp 2 ![(331980 : ℝ) / 31201, -33330 / 31201, 28380 / 31201] := by
  unfold normalResidual
  rw [witness_residual_one]
  ext i
  change (∑ j : Fin 4, witnessA j i *
    ![(331980 : ℝ) / 31201, -5555 / 31201, 5676 / 31201, 1] j) =
      ![(331980 : ℝ) / 31201, -33330 / 31201, 28380 / 31201] i
  fin_cases i <;>
    norm_num [witnessA, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_normalResidual_two : normalResidual witnessA witnessB witnessX₂ =
    WithLp.toLp 2 ![(519750 : ℝ) / 55219, 57750 / 55219, -145530 / 55219] := by
  unfold normalResidual
  rw [witness_residual_two]
  ext i
  change (∑ j : Fin 4, witnessA j i *
    ![(519750 : ℝ) / 55219, 9625 / 55219, -29106 / 55219, 1] j) =
      ![(519750 : ℝ) / 55219, 57750 / 55219, -145530 / 55219] i
  fin_cases i <;>
    norm_num [witnessA, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_normalResidual_three : normalResidual witnessA witnessB witnessX₃ = 0 := by
  unfold normalResidual
  rw [witness_residual_three]
  ext i
  change (∑ j : Fin 4, witnessA j i * ![(0 : ℝ), 0, 0, 1] j) = 0
  fin_cases i <;>
    norm_num [witnessA, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

theorem witnessX₁_ne_zero : witnessX₁ ≠ 0 := by
  intro h
  have hs := witnessX₁_norm_sq
  norm_num [h] at hs

theorem witnessX₂_ne_zero : witnessX₂ ≠ 0 := by
  intro h
  have hs := witnessX₂_norm_sq
  norm_num [h] at hs

theorem witnessX₃_ne_zero : witnessX₃ ≠ 0 := by
  intro h
  have hs := witnessX₃_norm_sq
  norm_num [h] at hs

private theorem first_krylov_membership : witnessX₁ ∈ krylov witnessA witnessB 1 := by
  have heq : witnessX₁ = ((1021 : ℝ) / 31201) • witnessGenerator 0 := by
    rw [generator_zero]
    ext i
    fin_cases i <;> norm_num [witnessX₁]
  rw [heq]
  exact (krylov witnessA witnessB 1).smul_mem _ (generator_mem (by norm_num))

private theorem second_krylov_membership : witnessX₂ ∈ krylov witnessA witnessB 2 := by
  have heq : witnessX₂ = ((16321 : ℝ) / 110438) • witnessGenerator 0 -
      ((383 : ℝ) / 110438) • witnessGenerator 1 := by
    rw [generator_zero, generator_one]
    ext i
    fin_cases i <;> norm_num [witnessX₂]
  rw [heq]
  exact (krylov witnessA witnessB 2).sub_mem
    ((krylov witnessA witnessB 2).smul_mem _ (generator_mem (by norm_num)))
    ((krylov witnessA witnessB 2).smul_mem _ (generator_mem (by norm_num)))

private theorem third_krylov_membership : witnessX₃ ∈ krylov witnessA witnessB 3 := by
  have heq : witnessX₃ = ((961 : ℝ) / 900) • witnessGenerator 0 -
      ((31 : ℝ) / 450) • witnessGenerator 1 + ((1 : ℝ) / 900) • witnessGenerator 2 := by
    rw [generator_zero, generator_one, generator_two]
    ext i
    fin_cases i <;> norm_num [witnessX₃]
  rw [heq]
  exact (krylov witnessA witnessB 3).add_mem
    ((krylov witnessA witnessB 3).sub_mem
      ((krylov witnessA witnessB 3).smul_mem _ (generator_mem (by norm_num)))
      ((krylov witnessA witnessB 3).smul_mem _ (generator_mem (by norm_num))))
    ((krylov witnessA witnessB 3).smul_mem _ (generator_mem (by norm_num)))

private theorem zeroth_isLSMR : IsLSMRIterate witnessA witnessB 0 0 := by
  apply isLSMR_of_normal_orthogonality witnessH_injective (Submodule.zero_mem _)
  apply normal_orthogonality_of_generators
  intro j hj
  omega

private theorem first_isLSMR : IsLSMRIterate witnessA witnessB 1 witnessX₁ := by
  apply isLSMR_of_normal_orthogonality witnessH_injective first_krylov_membership
  apply normal_orthogonality_of_generators
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  change ⟪normalResidual witnessA witnessB witnessX₁,
    (witnessA.transpose * witnessA).toEuclideanLin (witnessGenerator 0)⟫_ℝ = 0
  rw [witness_normalResidual_one, generator_zero, witness_gram]
  norm_num [inner_eq_sum, euclidean_apply_coord, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.cons_val_three]

private theorem second_isLSMR : IsLSMRIterate witnessA witnessB 2 witnessX₂ := by
  apply isLSMR_of_normal_orthogonality witnessH_injective second_krylov_membership
  apply normal_orthogonality_of_generators
  intro j hj
  change ⟪normalResidual witnessA witnessB witnessX₂,
    (witnessA.transpose * witnessA).toEuclideanLin (witnessGenerator j)⟫_ℝ = 0
  interval_cases j
  · rw [witness_normalResidual_two, generator_zero, witness_gram]
    norm_num [inner_eq_sum, euclidean_apply_coord, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · rw [witness_normalResidual_two, generator_one, witness_gram]
    norm_num [inner_eq_sum, euclidean_apply_coord, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem third_isLSMR : IsLSMRIterate witnessA witnessB 3 witnessX₃ := by
  apply isLSMR_of_normal_orthogonality witnessH_injective third_krylov_membership
  intro y hy
  rw [witness_normalResidual_three]
  simp

private theorem normalResidual_zero_ne_zero : normalResidual witnessA witnessB 0 ≠ 0 := by
  rw [witness_normalResidual_zero]
  intro h
  have hc := congrArg (fun z : Vec 3 => z 0) h
  norm_num at hc

theorem normalResidual_one_ne_zero : normalResidual witnessA witnessB witnessX₁ ≠ 0 := by
  rw [witness_normalResidual_one]
  intro h
  have hc := congrArg (fun z : Vec 3 => z 0) h
  norm_num at hc

theorem normalResidual_two_ne_zero : normalResidual witnessA witnessB witnessX₂ ≠ 0 := by
  rw [witness_normalResidual_two]
  intro h
  have hc := congrArg (fun z : Vec 3 => z 0) h
  norm_num at hc

/-- The complete exact run, from zero through its first least-squares solution.
The minimization quantifiers include every real vector in each Krylov subspace. -/
theorem witness_run_exact :
    IsTerminatingLSMRRun witnessA witnessB witnessRun ∧
    witnessX₁ ≠ 0 ∧ witnessX₂ ≠ 0 ∧ witnessX₃ ≠ 0 := by
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, witnessX₁_ne_zero, witnessX₂_ne_zero, witnessX₃_ne_zero⟩
  · intro k
    fin_cases k
    · exact zeroth_isLSMR
    · exact first_isLSMR
    · exact second_isLSMR
    · exact third_isLSMR
  · intro k hk
    fin_cases k
    · exact normalResidual_zero_ne_zero
    · exact normalResidual_one_ne_zero
    · exact normalResidual_two_ne_zero
    · change (3 : ℕ) < 3 at hk
      omega
  · exact witness_normalResidual_three

#assert_trust kernel witnessA_injective
#assert_trust kernel witness_run_exact

end NLA.IE17
