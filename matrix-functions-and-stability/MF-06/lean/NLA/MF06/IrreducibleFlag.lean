/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

C15 combines the actual saturated common-invariant chain, adapted basis,
surjective labels, inverse coordinate matrices, and quotient irreducibility.
The family may be infinite or empty; no compactness assumption is added.
-/
import NLA.MF06.FlagIrreducibility

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem irreducible_flag {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d)) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ d ∧
      ∃ b : Fin d → Fin r, Function.Surjective b ∧
        ∃ Q R : Square d, Q * R = 1 ∧ R * Q = 1 ∧
          (∀ A ∈ conjugateFamily Q R M, IsUpperBlockTriangular b A) ∧
          ∀ i : Fin r, FamilyIrreducible (diagonalFamily b i (conjugateFamily Q R M)) := by
  obtain ⟨r, hr, hrd, F, h0, htop, hstrict, hinv, hsat⟩ :=
    exists_saturated_invariant_chain hd M
  obtain ⟨B, hspanB⟩ := exists_basis_spanning_chain F hstrict.monotone h0 htop
  obtain ⟨b, hsurj, hmem, hspan⟩ := basis_chain_labeling F hstrict h0 htop B hspanB
  have hupper := inBasis_upper_of_flag F B b hmem hspan M hinv
  have hfamily : conjugateFamily (basisForward B) (basisBackward B) M =
      inBasis B '' M := by
    unfold conjugateFamily
    have hmap : (fun A : Square d => basisBackward B * A * basisForward B) =
        inBasis B := by
      funext A
      exact (inBasis_eq_conjugate B A).symm
    rw [hmap]
  refine ⟨r, hr, hrd, b, hsurj, basisForward B, basisBackward B,
    basisForward_mul_backward B, basisBackward_mul_forward B, ?_, ?_⟩
  · rw [hfamily]
    rintro _ ⟨A, hA, rfl⟩
    exact hupper A hA
  · rw [hfamily]
    exact diagonal_irreducible_of_saturated_flag F hstrict.monotone B b hspan M hinv
      hupper hsat

#print axioms irreducible_flag
#assert_trust kernel irreducible_flag

end NLA.MF06
