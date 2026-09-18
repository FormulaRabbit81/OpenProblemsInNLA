/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The exact row-exchange identity, obtained by transposing the column identity.
-/
import NLA.NM04.MinorColumnExchange
import NLA.NM04.MinorTranspose
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

theorem minor_row_exchange_identity {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I (Matrix.vecMulVec (fun _ => 1) (fun j => ∑ i, T i j)) =
      (I.1.1.card : 𝕜) * minor T I + rowExchange (minor T) I := by
  let Z : Matrix α β 𝕜 := Matrix.vecMulVec (fun _ => 1) (fun j => ∑ i, T i j)
  have hZ : Matrix.vecMulVec (fun j => ∑ i, Tᵀ j i) (fun _ => 1) = Zᵀ := by
    ext j i
    simp only [Z, Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_one, one_mul]
  calc
    _ = cofactorForm Tᵀ (minorTransposeIndex I) Zᵀ := (cofactorForm_transpose T I Z).symm
    _ = cofactorForm Tᵀ (minorTransposeIndex I)
        (Matrix.vecMulVec (fun j => ∑ i, Tᵀ j i) (fun _ => 1)) :=
      congrArg (cofactorForm Tᵀ (minorTransposeIndex I)) hZ.symm
    _ = (I.1.2.card : 𝕜) * minor Tᵀ (minorTransposeIndex I) +
        columnExchange (minor Tᵀ) (minorTransposeIndex I) :=
      minor_column_exchange_identity Tᵀ (minorTransposeIndex I)
    _ = _ := congrArg₂ (· + ·)
      (congrArg₂ (· * ·) (congrArg (fun n : ℕ => (n : 𝕜)) I.property.symm)
        (minor_transpose T I))
      (columnExchange_transpose T I)

#print axioms minor_row_exchange_identity
#assert_trust kernel minor_row_exchange_identity

end
end NLA.NM04
