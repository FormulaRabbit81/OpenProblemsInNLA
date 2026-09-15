/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP05

lemma dot_self_smul {n : ℕ} (c : ℝ) (v : Vec n) :
    dotProduct (c • v) (c • v) = c^2 * dotProduct v v := by
  rw [smul_dotProduct, dotProduct_smul]
  simp [pow_two, mul_assoc]

lemma rayleigh_smul {n : ℕ} (K : Operator n) (v : Vec n) (c : ℝ) (hc : c ≠ 0) :
    rayleigh K (c • v) = rayleigh K v := by
  unfold rayleigh
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, dot_self_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← pow_two, mul_div_mul_left _ _ (pow_ne_zero _ hc)]

lemma normalize_sector {n : ℕ} {v : Vec n} {ε : ℝ} (hv : v ≠ 0)
    (hs : commutationMatrix n *ᵥ v = ε • v) :
    ∃ w : Vec n, dotProduct w w = 1 ∧ commutationMatrix n *ᵥ w = ε • w ∧
      ∀ K : Operator n, rayleigh K w = rayleigh K v := by
  let d := Real.sqrt (dotProduct v v)
  have hd : 0 < d := Real.sqrt_pos.2 (dot_self_pos hv)
  refine ⟨d⁻¹ • v, ?_, ?_, ?_⟩
  · rw [dot_self_smul]
    have hsqr : d^2 = dotProduct v v := Real.sq_sqrt (le_of_lt (dot_self_pos hv))
    rw [← hsqr]
    field_simp
  · rw [Matrix.mulVec_smul, hs, smul_smul, smul_smul, mul_comm]
  · intro K
    exact rayleigh_smul K v d⁻¹ (inv_ne_zero hd.ne')

/-- The actual Euclidean unit sector, expressed by its dot-product square. -/
def unitSector (n : ℕ) (ε : ℝ) : Set (Vec n) :=
  {v | dotProduct v v = 1 ∧ commutationMatrix n *ᵥ v = ε • v}

lemma unitSector_isCompact (n : ℕ) (ε : ℝ) : IsCompact (unitSector n ε) := by
  have hs : IsClosed (unitSector n ε) := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  apply isCompact_Icc.of_isClosed_subset hs
  intro v hv
  have hcoord (i : Fin n × Fin n) : -1 ≤ v i ∧ v i ≤ 1 := by
    have ht : v i * v i ≤ dotProduct v v :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
    rw [hv.1] at ht
    constructor <;> nlinarith
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩

lemma unitSector_ne_zero {n : ℕ} {ε : ℝ} {v : Vec n} (hv : v ∈ unitSector n ε) : v ≠ 0 := by
  intro h
  simpa [h] using hv.1

lemma sector_minimum_exists {n : ℕ} (A B : Mat n) (ε : ℝ)
    (hne : ∃ v : Vec n, v ≠ 0 ∧ commutationMatrix n *ᵥ v = ε • v) :
    ∃ a : ℝ, IsLeast (sectorValues A B ε) a := by
  obtain ⟨v, hv, he⟩ := hne
  obtain ⟨w, hw, hwe, _⟩ := normalize_sector hv he
  have hs : (unitSector n ε).Nonempty := ⟨w, hw, hwe⟩
  let f : Vec n → ℝ := fun v => dotProduct v (Matrix.kronecker A B *ᵥ v)
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨u, hu, hmin⟩ := (unitSector_isCompact n ε).exists_isMinOn hs hf.continuousOn
  have hur : rayleigh (Matrix.kronecker A B) u = f u := by simp [rayleigh, hu.1, f]
  refine ⟨f u, ?_, ?_⟩
  · exact ⟨u, unitSector_ne_zero hu, hu.2, hur.symm⟩
  · rintro z ⟨v, hv, hve, rfl⟩
    obtain ⟨w, hw, hwe, heq⟩ := normalize_sector hv hve
    have hwr : rayleigh (Matrix.kronecker A B) w = f w := by simp [rayleigh, hw, f]
    rw [← heq (Matrix.kronecker A B), hwr]
    exact hmin ⟨hw, hwe⟩

lemma symmetric_sector_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : Vec n, v ≠ 0 ∧ commutationMatrix n *ᵥ v = (1 : ℝ) • v := by
  have hI : (1 : Mat n) ≠ 0 := by
    intro h
    have hi := congrFun (congrFun h (⟨0, by omega⟩ : Fin n)) (⟨0, by omega⟩ : Fin n)
    simp at hi
  refine ⟨columnVec (1 : Mat n), columnVec_ne_zero hI, ?_⟩
  rw [commutation_columnVec, Matrix.transpose_one, one_smul]

lemma skew_sector_nonempty (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Vec n, v ≠ 0 ∧ commutationMatrix n *ᵥ v = (-1 : ℝ) • v := by
  refine ⟨columnVec (skewExample n), columnVec_ne_zero (skew_ne_zero n hn), ?_⟩
  rw [commutation_columnVec, skew_transpose]
  simp only [columnVec, Matrix.vec_neg, neg_one_smul]

lemma both_sector_minima (n : ℕ) (hn : 2 ≤ n) (A B : Mat n) :
    ∃ a b : ℝ, IsLeast (sectorValues A B 1) a ∧ IsLeast (sectorValues A B (-1)) b := by
  obtain ⟨a, ha⟩ := sector_minimum_exists A B 1 (symmetric_sector_nonempty n (by omega))
  obtain ⟨b, hb⟩ := sector_minimum_exists A B (-1) (skew_sector_nonempty n hn)
  exact ⟨a, b, ha, hb⟩

lemma commutation_dot {n : ℕ} (v w : Vec n) :
    dotProduct (commutationMatrix n *ᵥ v) (commutationMatrix n *ᵥ w) = dotProduct v w := by
  rw [commutation_mulVec, commutation_mulVec]
  exact comp_equiv_dotProduct_comp_equiv v w (Equiv.prodComm (Fin n) (Fin n))

lemma commutation_kronecker {n : ℕ} (A B : Mat n) (v : Vec n) :
    commutationMatrix n *ᵥ (Matrix.kronecker A B *ᵥ v) =
      Matrix.kronecker B A *ᵥ (commutationMatrix n *ᵥ v) := by
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.surjective v
  change commutationMatrix n *ᵥ (Matrix.kronecker A B *ᵥ columnVec X) =
    Matrix.kronecker B A *ᵥ (commutationMatrix n *ᵥ columnVec X)
  rw [kronecker_columnVec, commutation_columnVec, commutation_columnVec,
    kronecker_columnVec]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma sector_rayleigh_twice {n : ℕ} (A B : Mat n) {v : Vec n} {ε : ℝ}
    (he : ε^2 = 1) (hv : commutationMatrix n *ᵥ v = ε • v) :
    rayleigh (jordanMatrix A B) v = 2 * rayleigh (Matrix.kronecker A B) v := by
  have h := commutation_dot v (Matrix.kronecker A B *ᵥ v)
  rw [commutation_kronecker, hv, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  rw [← mul_assoc, ← pow_two, he, one_mul] at h
  unfold rayleigh jordanMatrix
  rw [Matrix.add_mulVec, dotProduct_add, h]
  ring

lemma rayleigh_of_eigenvector {n : ℕ} (K : Operator n) {v : Vec n} (hv : v ≠ 0)
    {μ : ℝ} (he : K *ᵥ v = μ • v) : rayleigh K v = μ := by
  unfold rayleigh
  rw [he, dotProduct_smul]
  simp only [smul_eq_mul]
  exact mul_div_cancel_right₀ μ (dot_self_pos hv).ne'

/-- The global PSD minimum gives the exact original attained two-sector comparison. -/
lemma sector_comparison_of_psd_minimizer (n : ℕ) (hn : 2 ≤ n) (A B : Mat n)
    (hm : ∃ μ : ℝ, ∃ X : Mat n, 0 < μ ∧ X.PosSemidef ∧ X ≠ 0 ∧
      jordanMatrix A B *ᵥ columnVec X = μ • columnVec X ∧
      ∀ v : Vec n, v ≠ 0 → μ ≤ rayleigh (jordanMatrix A B) v) :
    ∃ a b : ℝ, IsLeast (sectorValues A B 1) a ∧
      IsLeast (sectorValues A B (-1)) b ∧ a ≤ b := by
  obtain ⟨a, b, ha, hb⟩ := both_sector_minima n hn A B
  obtain ⟨μ, X, _, hX, hX0, hXe, hmin⟩ := hm
  have hv0 := columnVec_ne_zero hX0
  have hsym : Xᵀ = X := by simpa using hX.isHermitian.eq
  have hv : commutationMatrix n *ᵥ columnVec X = (1 : ℝ) • columnVec X := by
    rw [commutation_columnVec, hsym, one_smul]
  have hval := rayleigh_of_eigenvector (jordanMatrix A B) hv0 hXe
  have htwo := sector_rayleigh_twice A B (by norm_num : (1 : ℝ)^2=1) hv
  have hamem : μ / 2 ∈ sectorValues A B 1 := by
    refine ⟨columnVec X, hv0, hv, ?_⟩
    linarith
  have haμ : a ≤ μ / 2 := ha.2 hamem
  obtain ⟨v, hv0, hv, hbe⟩ := hb.1
  have hμ := hmin v hv0
  have htwo := sector_rayleigh_twice A B (by norm_num : (-1 : ℝ)^2=1) hv
  refine ⟨a, b, ha, hb, ?_⟩
  linarith

end NLA.SP05
