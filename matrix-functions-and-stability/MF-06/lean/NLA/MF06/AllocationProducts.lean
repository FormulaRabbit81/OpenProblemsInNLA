/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Allocation words retain the same original letters in every component. Their
products are tensors of the diagonal-block words, whether or not the original
matrices are triangular. Symbolic compound and entry bounds give one fixed
constant for every word length, including zero and degree-zero factors.
-/
import NLA.MF06.AllocationAlgebra
import NLA.MF06.CompoundNorm
import NLA.MF06.WordImages
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma continuous_compoundMatrix {d : ℕ} (k : ℕ) : Continuous (compoundMatrix (d := d) k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Square d =>
    (A.submatrix (minorCoordinate d k i) (minorCoordinate d k j)).det)
  exact (continuous_id.matrix_submatrix (minorCoordinate d k i)
    (minorCoordinate d k j)).matrix_det

lemma continuous_allocationMatrix {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    Continuous (allocationMatrix b a) := by
  apply continuous_pi
  intro u
  apply continuous_pi
  intro v
  apply continuous_finsetProd
  intro i _
  exact (continuous_apply_apply (allocationCoordinate b a u i)
    (allocationCoordinate b a v i)).comp
      ((continuous_compoundMatrix (a i).val).comp (continuous_blockMatrix b i))

lemma allocation_word_product {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (w : List (Square d)) :
    matrixProduct (w.map (allocationMatrix b a)) =
      allocationTensor b a (fun i => matrixProduct (w.map (blockMatrix b i))) := by
  induction w with
  | nil =>
      simp only [List.map_nil, matrixProduct_nil]
      exact (allocationTensor_one b a).symm
  | cons A w ih =>
      simp only [List.map_cons, matrixProduct_cons, ih,
        allocationMatrix_eq_allocationTensor]
      exact (allocationTensor_mul b a _ _).symm

lemma allocationTensor_norm_bound {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (P : ∀ i : Fin r, Square (blockDim b i)) (K : Fin r → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hP : ∀ i, spectralNorm (P i) ≤ K i) :
    spectralNorm (allocationTensor b a P) ≤ (allocationDim b a : ℝ) *
      ∏ i : Fin r, compoundNormConstant (blockDim b i) (a i).val * K i ^ (a i).val := by
  have hc (i : Fin r) := compound_norm_bound (a i).val
    (Nat.le_of_lt_succ (a i).isLt) (P i)
  have hentry (i : Fin r) (u v : Fin (compoundDim (blockDim b i) (a i).val)) :
      ‖compoundMatrix (a i).val (P i) u v‖ ≤
        compoundNormConstant (blockDim b i) (a i).val * K i ^ (a i).val := by
    apply (spectralNorm_entry_bound _ u v).trans
    apply (hc i).2.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (spectralNorm_nonneg _) (hP i) _) (hc i).1.le
  apply spectralNorm_le_card_mul_entry_bound
  · exact Finset.prod_nonneg fun i _ => mul_nonneg (hc i).1.le (pow_nonneg (hK i) _)
  · intro u v
    change ‖∏ i : Fin r, compoundMatrix (a i).val (P i)
      (allocationCoordinate b a u i) (allocationCoordinate b a v i)‖ ≤ _
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hentry i _ _)

theorem allocation_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (a : Allocation b) :
    IsProductBounded (allocationFamily b a M) := by
  classical
  simp only [IsProductBounded] at hdiag
  choose K hK hbound using hdiag
  let C : ℝ := (allocationDim b a : ℝ) *
    ∏ i : Fin r, compoundNormConstant (blockDim b i) (a i).val * K i ^ (a i).val
  have hwords (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map (allocationMatrix b a))) ≤ C := by
    rw [allocation_word_product]
    apply allocationTensor_norm_bound b a _ K (fun i => zero_le_one.trans (hK i))
    intro i
    apply (word_le_familyGrowth (diagonalFamily b i M) (diagonalFamily_isCompact b i M hM)
      w.length (w.map (blockMatrix b i)) (by simp only [List.length_map])
      (word_image_in M (blockMatrix b i) w hw)).trans
    exact hbound i w.length
  have hcompact : IsCompact (allocationFamily b a M) := hM.image (continuous_allocationMatrix b a)
  have hnonempty : (allocationFamily b a M).Nonempty := hneM.image _
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro n
  obtain ⟨w, _, hw, he⟩ := familyGrowth_attained (allocationFamily b a M) hcompact hnonempty n
  obtain ⟨v, hv, rfl⟩ := word_image_preimage M (allocationMatrix b a) w hw
  exact he.symm.trans_le ((hwords v hv).trans (le_max_right _ _))

#print axioms allocation_product_bounded
#assert_trust kernel allocation_product_bounded

end NLA.MF06
