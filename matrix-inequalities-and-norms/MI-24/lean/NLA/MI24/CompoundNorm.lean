/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The norm of the actual k-th compound is the product of the k largest positive
eigenvalues. We explicitly transport Mathlib's unordered eigenbasis indices to
its descending eigenvalue list, and prove the finite product maximum by sorting
each subset. No majorization, eigenvalue-ordering, or compound-norm oracle is used.
The empty product k = 0 is included in each statement.
-/
import NLA.MI24.CompoundSpectral

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI24

def spectrumIndexEquiv (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

def sortedSpectrum {n : ℕ} (A : Mat n) (hA : A.PosDef) (i : Fin n) : ℝ :=
  hA.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

def prefixProduct {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  ∏ i : Fin k, x (Fin.castLE hk i)

lemma sortedSpectrum_eq_eigenvalues {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (i : Fin n) :
    sortedSpectrum A hA i = hA.isHermitian.eigenvalues (spectrumIndexEquiv n i) := by
  simp only [sortedSpectrum, spectrumIndexEquiv, Equiv.trans_apply,
    Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  rfl

lemma sortedSpectrum_pos {n : ℕ} (A : Mat n) (hA : A.PosDef) (i : Fin n) :
    0 < sortedSpectrum A hA i := by
  rw [sortedSpectrum_eq_eigenvalues]
  exact hA.eigenvalues_pos _

lemma sortedSpectrum_antitone {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    Antitone (sortedSpectrum A hA) := by
  intro i j hij
  exact hA.isHermitian.eigenvalues₀_antitone
    ((Fin.castOrderIso (Fintype.card_fin n).symm).monotone hij)

lemma traceReal_eq_sum_sortedSpectrum {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    traceReal A = ∑ i : Fin n, sortedSpectrum A hA i := by
  have ht := traceReal_spectralPower A hA.posSemidef 1
  rw [spectralPower_one A hA] at ht
  simp only [Real.rpow_one] at ht
  rw [ht]
  symm
  calc
    _ = ∑ i : Fin n, hA.isHermitian.eigenvalues (spectrumIndexEquiv n i) :=
      Finset.sum_congr rfl (fun i _ => sortedSpectrum_eq_eigenvalues A hA i)
    _ = _ := Equiv.sum_comp (spectrumIndexEquiv n) hA.isHermitian.eigenvalues

lemma fin_orderEmbedding_val_le {k n : ℕ} (g : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (g i).val := by
  have haux : ∀ j (hj : j < k), j ≤ (g ⟨j, hj⟩).val := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hj' : j < k := Nat.lt_of_succ_lt hj
      have hprev := ih hj'
      -- Present the adjacent natural indices as elements of Fin k, which
      -- is the domain order expected by the embedding strictMono property.
      have hnext := g.strictMono (show (⟨j, hj'⟩ : Fin k) < ⟨j + 1, hj⟩ from
        Nat.lt_succ_self j)
      -- Expose the resulting Fin inequality as an inequality of natural
      -- values so omega can combine it with the induction hypothesis.
      change (g ⟨j, hj'⟩).val < (g ⟨j + 1, hj⟩).val at hnext
      omega
  exact haux i.val i.isLt

lemma prod_embedding_eq_subset {k n : ℕ} (x : Fin n → ℝ) (f : Fin k ↪ Fin n) :
    (∏ i : Fin k, x (f i)) =
      ∏ j ∈ (Set.powersetCard.ofFinEmb k (Fin n) f).val, x j := by
  simp only [Set.powersetCard.val_ofFinEmb, Finset.prod_map]

lemma prod_embedding_le_prefix {k n : ℕ} (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : Antitone x) (f : Fin k ↪ Fin n) :
    (∏ i : Fin k, x (f i)) ≤ prefixProduct x k hk := by
  let s := Set.powersetCard.ofFinEmb k (Fin n) f
  let g : Fin k ↪o Fin n := Set.powersetCard.ofFinEmbEquiv.symm s
  have hg : Set.powersetCard.ofFinEmb k (Fin n) g.toEmbedding = s :=
    Set.powersetCard.ofFinEmbEquiv.apply_symm_apply s
  have hprod : (∏ i : Fin k, x (f i)) = ∏ i : Fin k, x (g i) := by
    -- Present the order embedding through its underlying Embedding,
    -- the interface required by the subset-product reindexing lemma.
    change (∏ i : Fin k, x (f i)) = ∏ i : Fin k, x (g.toEmbedding i)
    rw [prod_embedding_eq_subset x f, prod_embedding_eq_subset x g.toEmbedding, hg]
  rw [hprod]
  apply Finset.prod_le_prod (fun i _ => hx (g i))
  intro i _
  -- Lift the proved inequality of underlying natural values back to
  -- the Fin n order expected by the antitone sequence hypothesis.
  exact hs (show Fin.castLE hk i ≤ g i from fin_orderEmbedding_val_le g i)

lemma compoundDiagonal_realizes_embedding {k n : ℕ} (x : Fin n → ℝ)
    (f : Fin k ↪ Fin n) :
    ∃ i : Fin (compoundDim n k), compoundDiagonal k x i = ∏ a : Fin k, x (f a) := by
  let s := Set.powersetCard.ofFinEmb k (Fin n) f
  let i : Fin (compoundDim n k) := Fintype.equivFin (ExteriorIndex n k) s
  have hi : compoundIndex n k i = s :=
    (Fintype.equivFin (ExteriorIndex n k)).symm_apply_apply s
  have hg : Set.powersetCard.ofFinEmb k (Fin n) (minorCoordinate n k i).toEmbedding = s := by
    -- Expand minorCoordinate through the inverse finite-subset equivalence;
    -- this exposes the exact apply_symm_apply pair rather than a new identity.
    change Set.powersetCard.ofFinEmbEquiv
      (Set.powersetCard.ofFinEmbEquiv.symm (compoundIndex n k i)) = s
    rw [Equiv.apply_symm_apply, hi]
  refine ⟨i, ?_⟩
  -- Unfold compoundDiagonal into its product and expose the coordinate
  -- order embedding as an Embedding for the subset-product lemma.
  change (∏ a : Fin k, x ((minorCoordinate n k i).toEmbedding a)) = _
  rw [prod_embedding_eq_subset x (minorCoordinate n k i).toEmbedding,
    prod_embedding_eq_subset x f, hg]

lemma compoundDiagonal_le_sorted_prefix {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Mat n) (hA : A.PosDef) (i : Fin (compoundDim n k)) :
    compoundDiagonal k hA.isHermitian.eigenvalues i ≤
      prefixProduct (sortedSpectrum A hA) k hk := by
  let e := spectrumIndexEquiv n
  let f : Fin k ↪ Fin n := (minorCoordinate n k i).toEmbedding.trans e.symm.toEmbedding
  have hreindex (j : Fin n) :
      sortedSpectrum A hA (e.symm j) = hA.isHermitian.eigenvalues j := by
    rw [sortedSpectrum_eq_eigenvalues]
    exact congrArg hA.isHermitian.eigenvalues (e.apply_symm_apply j)
  calc
    _ = ∏ a : Fin k, sortedSpectrum A hA (f a) :=
      Finset.prod_congr rfl (fun a _ => (hreindex (minorCoordinate n k i a)).symm)
    _ ≤ _ := prod_embedding_le_prefix hk _ (fun j => (sortedSpectrum_pos A hA j).le)
      (sortedSpectrum_antitone A hA) f

lemma compoundDiagonal_attains_sorted_prefix {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Mat n) (hA : A.PosDef) :
    ∃ i : Fin (compoundDim n k), compoundDiagonal k hA.isHermitian.eigenvalues i =
      prefixProduct (sortedSpectrum A hA) k hk := by
  let f : Fin k ↪ Fin n :=
    (Fin.castLEOrderEmb hk).toEmbedding.trans (spectrumIndexEquiv n).toEmbedding
  obtain ⟨i, hi⟩ := compoundDiagonal_realizes_embedding hA.isHermitian.eigenvalues f
  refine ⟨i, hi.trans ?_⟩
  exact Finset.prod_congr rfl
    (fun a _ => (sortedSpectrum_eq_eigenvalues A hA (Fin.castLE hk a)).symm)

lemma infinitySchattenNorm_unitary_diagonal {n : ℕ} (U : unitary (Mat n))
    (x : Fin n → ℝ) :
    infinitySchattenNorm ((U : Mat n) * Matrix.diagonal (fun i => (x i : ℂ)) *
      star (U : Mat n)) = ‖(fun i => (x i : ℂ))‖ := by
  rw [infinitySchattenNorm_eq_l2, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

lemma infinitySchattenNorm_compound_eq_prefix {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Mat n) (hA : A.PosDef) :
    infinitySchattenNorm (compoundMatrix k A) =
      prefixProduct (sortedSpectrum A hA) k hk := by
  rw [compound_spectral_decomposition k A hA, infinitySchattenNorm_unitary_diagonal]
  have htop : 0 ≤ prefixProduct (sortedSpectrum A hA) k hk :=
    Finset.prod_nonneg fun i _ => (sortedSpectrum_pos A hA _).le
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg htop).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (compoundDiagonal_pos k _ hA.eigenvalues_pos i)]
    exact compoundDiagonal_le_sorted_prefix k hk A hA i
  · obtain ⟨i, hi⟩ := compoundDiagonal_attains_sorted_prefix k hk A hA
    have hnorm := norm_le_pi_norm
      (fun i => (compoundDiagonal k hA.isHermitian.eigenvalues i : ℂ)) i
    simpa only [Complex.norm_real, Real.norm_eq_abs, hi, abs_of_nonneg htop] using hnorm

end NLA.MI24
