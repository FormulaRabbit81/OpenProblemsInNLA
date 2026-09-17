/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original regularization argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Corollary 7.

Adjoining a positive scalar identity changes the actual radius to its maximum
with that scalar. Compression removes only scalar identities and records a
sublist, so every remaining generator retains its chronological position.
The argument uses the general exponential envelope, including at radius zero;
it does not assume continuity of the radius or any extremal norm.
-/
import NLA.MF05.RootLimit

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma familyGrowth_le_of_subset {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hN : IsCompact N) (hMN : M ⊆ N)
    (n : ℕ) : familyGrowth M n ≤ familyGrowth N n := by
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained M hM hne n
  rw [← he]
  exact word_le_familyGrowth N hN n w hw (fun A hA => hMN (hword A hA))

lemma jointSpectralRadius_le_of_subset {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hN : IsCompact N) (hMN : M ⊆ N) :
    jointSpectralRadius M ≤ jointSpectralRadius N := by
  have hneN : N.Nonempty := Set.Nonempty.mono hMN hne
  apply le_csInf (rootValues_nonempty N)
  rintro r ⟨n, hn, rfl⟩
  have hroot : rootGrowth M n ≤ rootGrowth N n := by
    apply (pow_le_pow_iff_left₀ (n := n) (rootGrowth_nonneg M hM hne n)
      (rootGrowth_nonneg N hN hneN n) (by omega)).mp
    rw [rootGrowth_pow M hM hne n hn, rootGrowth_pow N hN hneN n hn]
    exact familyGrowth_le_of_subset M N hM hne hN hMN n
  exact (jointSpectralRadius_le_root M hM hne n hn).trans hroot

/-- Removing scalar-identity letters leaves an order-preserving sublist over
the original family. The scalar exponent and residual length add to the
original length, and the displayed equality is an equality of matrices. -/
lemma identity_adjoin_word_compression {d : ℕ} (M : Set (Square d)) (e : ℝ)
    (w : List (Square d)) (hword : WordIn (identityAdjoin e M) w) :
    ∃ k : ℕ, ∃ u : List (Square d), WordIn M u ∧ u.Sublist w ∧
      k + u.length = w.length ∧
      matrixProduct w = (e : ℂ) ^ k • matrixProduct u := by
  induction w with
  | nil =>
      refine ⟨0, [], WordIn_nil M, List.Sublist.slnil, ?_, ?_⟩ <;> simp
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff (identityAdjoin e M) A w).mp hword
      obtain ⟨k, u, hu, hsub, hlen, hprod⟩ := ih hw
      rcases Set.mem_insert_iff.mp hA with rfl | hA
      · refine ⟨k + 1, u, hu, hsub.cons _, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · simp only [matrixProduct_cons, hprod, Matrix.mul_smul,
            mul_one, smul_smul, pow_succ]
          rw [mul_comm]
      · refine ⟨k, A :: u, (WordIn_cons_iff M A u).mpr ⟨hA, hu⟩,
          hsub.cons_cons A, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · simp only [matrixProduct_cons, hprod, Matrix.smul_mul]

/-- Every compressed word uses the same envelope coefficient. Scalar-identity
letters cost at most the chosen discount, even when the old radius is zero. -/
lemma identity_adjoin_growth_bound {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (e a K : ℝ) (he : 0 ≤ e) (hea : e ≤ a)
    (hbound : ∀ n : ℕ, familyGrowth M n ≤ K * a ^ n) (n : ℕ) :
    familyGrowth (identityAdjoin e M) n ≤ K * a ^ n := by
  have hN : IsCompact (identityAdjoin e M) := hM.insert _
  have hneN : (identityAdjoin e M).Nonempty := Set.insert_nonempty _ _
  obtain ⟨w, hw, hword, heq⟩ := familyGrowth_attained _ hN hneN n
  obtain ⟨k, u, hu, _, hlen, hprod⟩ := identity_adjoin_word_compression M e w hword
  have hu_bound : spectralNorm (matrixProduct u) ≤ K * a ^ u.length :=
    (word_le_familyGrowth M hM u.length u rfl hu).trans (hbound u.length)
  rw [← heq, hprod, spectralNorm_smul, norm_pow, Complex.norm_of_nonneg he]
  calc
    e ^ k * spectralNorm (matrixProduct u) ≤ a ^ k * (K * a ^ u.length) :=
      mul_le_mul (pow_le_pow_left₀ he hea k) hu_bound (spectralNorm_nonneg _)
        (pow_nonneg (he.trans hea) k)
    _ = K * a ^ n := by rw [mul_left_comm, ← pow_add, hlen, hw]

lemma scalar_identity_replicate_product {d : ℕ} (c : ℂ) (n : ℕ) :
    matrixProduct (List.replicate n (c • (1 : Square d))) = c ^ n • (1 : Square d) := by
  simp only [matrixProduct, List.reverse_replicate, List.prod_replicate, smul_pow, one_pow]

/-- The repeated scalar-identity word provides a lower bound at every positive
index of the actual root infimum. No positive radius is assumed. -/
lemma scalar_identity_le_radius {d : ℕ} (hd : 1 ≤ d) (N : Set (Square d))
    (hN : IsCompact N) (e : ℝ) (he : 0 ≤ e) (hI : (e : ℂ) • (1 : Square d) ∈ N) :
    e ≤ jointSpectralRadius N := by
  have hneN : N.Nonempty := ⟨_, hI⟩
  apply le_csInf (rootValues_nonempty N)
  rintro r ⟨n, hn, rfl⟩
  apply (pow_le_pow_iff_left₀ (n := n) he (rootGrowth_nonneg N hN hneN n)
    (by omega)).mp
  rw [rootGrowth_pow N hN hneN n hn]
  have hword : WordIn N (List.replicate n ((e : ℂ) • (1 : Square d))) := by
    intro A hA
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hA
    exact hI
  have hbound := word_le_familyGrowth N hN n
    (List.replicate n ((e : ℂ) • (1 : Square d))) List.length_replicate hword
  simpa only [scalar_identity_replicate_product, spectralNorm_smul, norm_pow,
    Complex.norm_of_nonneg he, spectralNorm_one hd, mul_one] using hbound

theorem scalar_identity_adjoin_radius {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (e : ℝ) (he : 0 < e) :
    IsCompact (identityAdjoin e M) ∧ (identityAdjoin e M).Nonempty ∧
    familyNorm (identityAdjoin e M) = max (familyNorm M) e ∧
    jointSpectralRadius (identityAdjoin e M) = max (jointSpectralRadius M) e := by
  have hN : IsCompact (identityAdjoin e M) := hM.insert _
  have hneN : (identityAdjoin e M).Nonempty := Set.insert_nonempty _ _
  have hidnorm : spectralNorm ((e : ℂ) • (1 : Square d)) = e := by
    rw [spectralNorm_smul, Complex.norm_of_nonneg he.le, spectralNorm_one hd, mul_one]
  have hnorm : familyNorm (identityAdjoin e M) = max (familyNorm M) e := by
    unfold familyNorm identityAdjoin
    rw [Set.image_insert_eq,
      csSup_insert (hM.image continuous_spectralNorm).bddAbove (hne.image spectralNorm),
      hidnorm]
    exact max_comm e _
  have hupper : jointSpectralRadius (identityAdjoin e M) ≤ max (jointSpectralRadius M) e := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have hra : jointSpectralRadius M < a := (le_max_left _ _).trans_lt ha
    have hea : e ≤ a := ((le_max_right _ _).trans_lt ha).le
    obtain ⟨ha0, K, hK, hbound⟩ := general_exponential_envelope hd M hM hne a hra
    exact exponential_bound_controls_radius hd _ hN hneN K a hK ha0
      (identity_adjoin_growth_bound M hM e a K he.le hea hbound)
  have hMlower : jointSpectralRadius M ≤ jointSpectralRadius (identityAdjoin e M) :=
    jointSpectralRadius_le_of_subset M _ hM hne hN (Set.subset_insert _ _)
  have helower : e ≤ jointSpectralRadius (identityAdjoin e M) :=
    scalar_identity_le_radius hd _ hN e he.le (Set.mem_insert _ _)
  exact ⟨hN, hneN, hnorm, le_antisymm hupper (max_le hMlower helower)⟩

#print axioms identity_adjoin_word_compression
#assert_trust kernel identity_adjoin_word_compression
#print axioms scalar_identity_adjoin_radius
#assert_trust kernel scalar_identity_adjoin_radius

end NLA.MF05
