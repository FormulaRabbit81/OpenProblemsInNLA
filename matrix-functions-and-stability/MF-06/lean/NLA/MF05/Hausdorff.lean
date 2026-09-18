/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Theorem 2.

The canonical spectral sup-inf formula is identified with Mathlib's actual
operator Hausdorff distance. Nonempty compactness excludes its total-definition
fallback; nearest generators are attained. No numerical approximation is used.
-/
import NLA.MF05.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma continuous_spectral_operator {d : ℕ} :
    Continuous (fun A : Square d => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A) := by
  let f : Square d →ₗ[ℂ] (EuclideanVector d →L[ℂ] EuclideanVector d) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional

lemma spectral_operator_distance {d : ℕ} (A B : Square d) :
    dist (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B) = spectralNorm (A - B) := by
  simp only [dist_eq_norm, spectralNorm, map_sub]

lemma spectralImage_isCompact {d : ℕ} (M : Set (Square d)) (hM : IsCompact M) :
    IsCompact (spectralImage M) := hM.image continuous_spectral_operator

lemma spectralImage_nonempty {d : ℕ} (M : Set (Square d)) (hne : M.Nonempty) :
    (spectralImage M).Nonempty := hne.image _

lemma spectral_hausdorff_finite {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty) :
    Metric.hausdorffEDist (spectralImage M) (spectralImage N) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (spectralImage_nonempty M hneM) (spectralImage_nonempty N hneN)
    (spectralImage_isCompact M hM).isBounded (spectralImage_isCompact N hN).isBounded

lemma pointFamilyDistance_eq_infDist {d : ℕ} (A : Square d)
    (N : Set (Square d)) (hneN : N.Nonempty) :
    pointFamilyDistance A N =
      Metric.infDist (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A) (spectralImage N) := by
  let f := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  have himage : ((fun B => dist (f A) B) '' spectralImage N) =
      ((fun B : Square d => spectralNorm (A - B)) '' N) := by
    ext r
    constructor
    · rintro ⟨B, ⟨C, hC, rfl⟩, rfl⟩
      exact ⟨C, hC, (spectral_operator_distance A C).symm⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨f B, ⟨B, hB, rfl⟩, spectral_operator_distance A B⟩
  unfold pointFamilyDistance
  rw [← himage]
  exact (Metric.isGLB_infDist (spectralImage_nonempty N hneN)).csInf_eq
    ((spectralImage_nonempty N hneN).image _)

lemma pointFamilyDistance_le_hausdorff {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (A : Square d) (hA : A ∈ M) : pointFamilyDistance A N ≤ spectralHausdorff M N := by
  rw [pointFamilyDistance_eq_infDist A N hneN]
  exact Metric.infDist_le_hausdorffDist_of_mem ⟨A, hA, rfl⟩
    (spectral_hausdorff_finite M N hM hneM hN hneN)

lemma spectral_nearest_generator {d : ℕ} (A : Square d) (N : Set (Square d))
    (hN : IsCompact N) (hneN : N.Nonempty) :
    ∃ B ∈ N, pointFamilyDistance A N = spectralNorm (A - B) := by
  obtain ⟨B, ⟨C, hC, rfl⟩, hmin⟩ :=
    (spectralImage_isCompact N hN).exists_infDist_eq_dist
      (spectralImage_nonempty N hneN) (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
  exact ⟨C, hC, (pointFamilyDistance_eq_infDist A N hneN).trans
    (hmin.trans (spectral_operator_distance A C))⟩

lemma spectralHausdorff_eq_canonical {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty) :
    spectralHausdorff M N = canonicalHausdorff M N := by
  have hMN := pointFamilyDistance_le_hausdorff M N hM hneM hN hneN
  have hNM (B : Square d) (hB : B ∈ N) : pointFamilyDistance B M ≤ spectralHausdorff M N := by
    calc
      pointFamilyDistance B M ≤ spectralHausdorff N M :=
        pointFamilyDistance_le_hausdorff N M hN hneN hM hneM B hB
      _ = spectralHausdorff M N := Metric.hausdorffDist_comm
  have hbMN : BddAbove ((fun A : Square d => pointFamilyDistance A N) '' M) := by
    refine ⟨spectralHausdorff M N, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    exact hMN A hA
  have hbNM : BddAbove ((fun B : Square d => pointFamilyDistance B M) '' N) := by
    refine ⟨spectralHausdorff M N, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    exact hNM B hB
  have hlMN (A : Square d) (hA : A ∈ M) :
      pointFamilyDistance A N ≤ directedSpectralDistance M N :=
    le_csSup hbMN ⟨A, hA, rfl⟩
  have hlNM (B : Square d) (hB : B ∈ N) :
      pointFamilyDistance B M ≤ directedSpectralDistance N M :=
    le_csSup hbNM ⟨B, hB, rfl⟩
  have hnonneg : 0 ≤ canonicalHausdorff M N := by
    obtain ⟨A, hA⟩ := hneM
    have hp : 0 ≤ pointFamilyDistance A N := by
      rw [pointFamilyDistance_eq_infDist A N hneN]
      exact Metric.infDist_nonneg
    exact hp.trans ((hlMN A hA).trans (le_max_left _ _))
  apply le_antisymm
  · apply Metric.hausdorffDist_le_of_infDist hnonneg
    · rintro A ⟨B, hB, rfl⟩
      rw [← pointFamilyDistance_eq_infDist B N hneN]
      exact (hlMN B hB).trans (le_max_left _ _)
    · rintro B ⟨A, hA, rfl⟩
      rw [← pointFamilyDistance_eq_infDist A M hneM]
      exact (hlNM A hA).trans (le_max_right _ _)
  · apply max_le
    · apply csSup_le (hneM.image _)
      rintro r ⟨A, hA, rfl⟩
      exact hMN A hA
    · apply csSup_le (hneN.image _)
      rintro r ⟨B, hB, rfl⟩
      exact hNM B hB

theorem spectral_hausdorff_semantics {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty) :
    IsCompact (spectralImage M) ∧ IsCompact (spectralImage N) ∧
    Metric.hausdorffEDist (spectralImage M) (spectralImage N) ≠ ⊤ ∧
    spectralHausdorff M N = canonicalHausdorff M N ∧
    0 ≤ spectralHausdorff M N ∧
    spectralHausdorff M N = spectralHausdorff N M ∧
    (spectralHausdorff M N = 0 ↔ M = N) ∧
    (∀ A ∈ M, ∃ B ∈ N,
      pointFamilyDistance A N = spectralNorm (A - B) ∧
      spectralNorm (A - B) ≤ spectralHausdorff M N) ∧
    (∀ B ∈ N, ∃ A ∈ M,
      pointFamilyDistance B M = spectralNorm (B - A) ∧
      spectralNorm (B - A) ≤ spectralHausdorff M N) := by
  have hcM := spectralImage_isCompact M hM
  have hcN := spectralImage_isCompact N hN
  have hfin := spectral_hausdorff_finite M N hM hneM hN hneN
  refine ⟨hcM, hcN, hfin, spectralHausdorff_eq_canonical M N hM hneM hN hneN,
    Metric.hausdorffDist_nonneg, Metric.hausdorffDist_comm, ?_, ?_, ?_⟩
  · have heq := hcM.isClosed.hausdorffDist_zero_iff_eq hcN.isClosed hfin
    constructor
    · intro h
      exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective.image_injective (heq.mp h)
    · rintro rfl
      exact Metric.hausdorffDist_self_zero
  · intro A hA
    obtain ⟨B, hB, heq⟩ := spectral_nearest_generator A N hN hneN
    exact ⟨B, hB, heq, heq ▸ pointFamilyDistance_le_hausdorff M N hM hneM hN hneN A hA⟩
  · intro B hB
    obtain ⟨A, hA, heq⟩ := spectral_nearest_generator B M hM hneM
    refine ⟨A, hA, heq, ?_⟩
    calc
      spectralNorm (B - A) ≤ spectralHausdorff N M :=
        heq ▸ pointFamilyDistance_le_hausdorff N M hN hneN hM hneM B hB
      _ = spectralHausdorff M N := Metric.hausdorffDist_comm

#print axioms spectral_hausdorff_semantics
#assert_trust kernel spectral_hausdorff_semantics

end NLA.MF05
