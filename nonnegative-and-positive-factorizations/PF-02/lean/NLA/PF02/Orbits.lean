/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Definitions
import Mathlib.Tactic

noncomputable section
open Matrix
namespace NLA.PF02

lemma congruent_refl {p q k : ℕ} {M : Mat p q} (F : Factorization M k) :
    Congruent F F := by
  refine ⟨1, ?_, ?_⟩ <;> intro i <;> simp

lemma congruent_symm {p q k : ℕ} {M : Mat p q} {F G : Factorization M k}
    (h : Congruent F G) : Congruent G F := by
  obtain ⟨S, hA, hB⟩ := h
  have hl : (↑(S⁻¹) : Mat k k).transpose * (↑S : Mat k k).transpose = 1 := by
    rw [← Matrix.transpose_mul]
    simp
  refine ⟨S⁻¹, ?_, ?_⟩
  · intro i
    rw [hA i]
    calc
      F.val.1 i = (↑(S⁻¹) : Mat k k).transpose * (↑S : Mat k k).transpose *
          F.val.1 i * ((↑S : Mat k k) * ↑(S⁻¹)) := by rw [hl]; simp
      _ = _ := by noncomm_ring
  · intro j
    simp only [inv_inv]
    rw [hB j]
    calc
      F.val.2 j = ((↑S : Mat k k) * ↑(S⁻¹)) * F.val.2 j *
          ((↑(S⁻¹) : Mat k k).transpose * (↑S : Mat k k).transpose) := by rw [hl]; simp
      _ = _ := by noncomm_ring

lemma congruent_trans {p q k : ℕ} {M : Mat p q} {F G H : Factorization M k}
    (hFG : Congruent F G) (hGH : Congruent G H) : Congruent F H := by
  obtain ⟨S, hSA, hSB⟩ := hFG
  obtain ⟨T, hTA, hTB⟩ := hGH
  refine ⟨S * T, ?_, ?_⟩
  · intro i
    rw [hTA i, hSA i]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro j
    rw [hTB j, hSB j]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma actual_orbit_eq_iff {p q k : ℕ} {M : Mat p q} (F G : Factorization M k) :
    Quot.mk (@Congruent p q k M) F = Quot.mk (@Congruent p q k M) G ↔ Congruent F G := by
  constructor
  · intro h
    have heq := Quot.eqvGen_exact h
    clear h
    induction heq with
    | rel _ _ h => exact h
    | refl a => exact congruent_refl a
    | symm _ _ _ h => exact congruent_symm h
    | trans _ _ _ _ _ h₁ h₂ => exact congruent_trans h₁ h₂
  · exact Quot.sound

lemma actual_orbit_semantics {p q k : ℕ} (M : Mat p q) :
    Topology.IsQuotientMap (@Quot.mk (Factorization M k) (@Congruent p q k M)) ∧
    (∀ F G : Factorization M k,
      Quot.mk (@Congruent p q k M) F = Quot.mk (@Congruent p q k M) G ↔ Congruent F G) :=
  ⟨isQuotientMap_quot_mk, actual_orbit_eq_iff⟩

end NLA.PF02
