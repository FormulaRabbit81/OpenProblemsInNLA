/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

An orbit consists of actual chronological products, including the empty word.
Its genuine complex linear span is invariant. Irreducibility then implies
spanning and a non-annihilating word for every nonzero operator and vector.
No finite orbit cutoff or extremal norm is assumed.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def wordOrbit {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) : Set (EuclideanVector d) :=
  {y | ∃ w : List (Square d), WordIn M w ∧ y = applyMatrix (matrixProduct w) x}

def orbitSpan {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) :
    Submodule ℂ (EuclideanVector d) := Submodule.span ℂ (wordOrbit M x)

lemma self_mem_orbitSpan {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) :
    x ∈ orbitSpan M x := by
  apply Submodule.subset_span
  exact ⟨[], WordIn_nil M, by simp only [matrixProduct_nil, applyMatrix_one]⟩

lemma orbitSpan_invariant {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) :
    FamilyInvariant M (orbitSpan M x) := by
  intro A hA y hy
  have hspan : orbitSpan M x ≤ (orbitSpan M x).comap
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    change applyMatrix A (applyMatrix (matrixProduct w) x) ∈ orbitSpan M x
    apply Submodule.subset_span
    refine ⟨w ++ [A], (WordIn_append_iff M w [A]).mpr
      ⟨hw, (WordIn_cons_iff M A []).mpr ⟨hA, WordIn_nil M⟩⟩, ?_⟩
    simp only [matrixProduct_append, matrixProduct_cons, matrixProduct_nil,
      one_mul, applyMatrix_mul]
  exact hspan hy

lemma irreducible_orbitSpan_eq_top {d : ℕ} (M : Set (Square d))
    (hirr : FamilyIrreducible M) (x : EuclideanVector d) (hx : x ≠ 0) :
    orbitSpan M x = ⊤ := by
  rcases hirr (orbitSpan M x) (orbitSpan_invariant M x) with hbot | htop
  · have hmem := self_mem_orbitSpan M x
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hx hmem).elim
  · exact htop

/-- Irreducibility supplies a real word witness, rather than an assumed
reachability constant. Compactness will later make these witnesses uniform. -/
lemma irreducible_word_not_annihilated {d : ℕ} (M : Set (Square d))
    (hirr : FamilyIrreducible M)
    (T : EuclideanVector d →L[ℂ] EuclideanVector d) (hT : T ≠ 0)
    (x : EuclideanVector d) (hx : x ≠ 0) :
    ∃ w : List (Square d), WordIn M w ∧ T (applyMatrix (matrixProduct w) x) ≠ 0 := by
  by_contra hnot
  have hall (w : List (Square d)) (hw : WordIn M w) :
      T (applyMatrix (matrixProduct w) x) = 0 := by
    by_contra hne
    exact hnot ⟨w, hw, hne⟩
  have hker : orbitSpan M x ≤ LinearMap.ker T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨w, hw, rfl⟩
    exact hall w hw
  have hzero : T = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    change T y = 0
    apply hker
    rw [irreducible_orbitSpan_eq_top M hirr x hx]
    exact Submodule.mem_top
  exact hT hzero

#print axioms irreducible_word_not_annihilated
#assert_trust kernel irreducible_word_not_annihilated

end NLA.MF06
