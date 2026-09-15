/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

noncomputable section
open Matrix
namespace NLA.PF02

/-- The full primal/dual change of basis, using the actual inverse of an arbitrary unit. -/
def changeBasis {p q k : ℕ} (S : (Mat k k)ˣ) (F : FactorTuple p q k) :
    FactorTuple p q k :=
  (fun i => (↑S : Mat k k).transpose * F.1 i * (↑S : Mat k k),
   fun j => (↑(S⁻¹) : Mat k k) * F.2 j * (↑(S⁻¹) : Mat k k).transpose)

/-- Every invertible real congruence preserves all PSD conditions and every trace equation. -/
theorem changeBasis_preserves_factorization {p q k : ℕ} {M : Mat p q}
    (S : (Mat k k)ˣ) (F : FactorTuple p q k) (hF : IsFactorization M F) :
    IsFactorization M (changeBasis S F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [changeBasis, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hF.1 i).conjTranspose_mul_mul_same (↑S : Mat k k)
  · intro j
    simpa [changeBasis, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hF.2.1 j).mul_mul_conjTranspose_same (↑(S⁻¹) : Mat k k)
  · intro i j
    change Matrix.trace (((↑S : Mat k k).transpose * F.1 i * (↑S : Mat k k)) *
      ((↑(S⁻¹) : Mat k k) * F.2 j * (↑(S⁻¹) : Mat k k).transpose)) = M i j
    have hleft : (↑(S⁻¹) : Mat k k).transpose * (↑S : Mat k k).transpose = 1 := by
      rw [← Matrix.transpose_mul]
      simp
    calc
      _ = Matrix.trace ((↑S : Mat k k).transpose *
          (F.1 i * ((↑S : Mat k k) * (↑(S⁻¹) : Mat k k)) * F.2 j) *
            (↑(S⁻¹) : Mat k k).transpose) := by congr 1; noncomm_ring
      _ = Matrix.trace ((↑S : Mat k k).transpose * (F.1 i * F.2 j) *
          (↑(S⁻¹) : Mat k k).transpose) := by simp
      _ = Matrix.trace ((↑(S⁻¹) : Mat k k).transpose * (↑S : Mat k k).transpose *
          (F.1 i * F.2 j)) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (F.1 i * F.2 j) := by rw [hleft, Matrix.one_mul]
      _ = M i j := hF.2.2 i j

/-- The change of basis acts on the full actual factorization subtype. -/
def changeBasisFactorization {p q k : ℕ} {M : Mat p q}
    (S : (Mat k k)ˣ) (F : Factorization M k) : Factorization M k :=
  ⟨changeBasis S F.val, changeBasis_preserves_factorization S F.val F.property⟩

/-- The constructed transformed factorization belongs to the exact single-congruence orbit. -/
theorem changeBasis_congruent {p q k : ℕ} {M : Mat p q}
    (S : (Mat k k)ˣ) (F : Factorization M k) :
    Congruent F (changeBasisFactorization S F) :=
  ⟨S, fun _ => rfl, fun _ => rfl⟩

/-- The literal relation is exactly equality with one actual transformed factorization. -/
theorem congruent_iff_changeBasis {p q k : ℕ} {M : Mat p q}
    (F G : Factorization M k) :
    Congruent F G ↔ ∃ S : (Mat k k)ˣ, G = changeBasisFactorization S F := by
  constructor
  · rintro ⟨S, hA, hB⟩
    refine ⟨S, Subtype.ext ?_⟩
    exact Prod.ext (funext hA) (funext hB)
  · rintro ⟨S, rfl⟩
    exact changeBasis_congruent S F

#assert_trust kernel changeBasis_preserves_factorization
#assert_trust kernel changeBasis_congruent
#assert_trust kernel congruent_iff_changeBasis
#print axioms changeBasis_preserves_factorization
#print axioms changeBasis_congruent
#print axioms congruent_iff_changeBasis

end NLA.PF02
