/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

The full complex normal-matrix spectral theorem, obtained from the commuting
Hermitian real and imaginary parts and the complete joint eigenbasis.
-/
import NLA.MI04.JointBasis
import Mathlib.LinearAlgebra.Complex.Module

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

/-- Keep the constructed parts opaque to the finite-dimensional basis assembly. -/
private lemma normal_operator_parts {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T) :
    ∃ A B : E →L[ℂ] E,
      (A : Module.End ℂ E).IsSymmetric ∧
      (B : Module.End ℂ E).IsSymmetric ∧ Commute A B ∧
      T = A + Complex.I • B := by
  let A : E →L[ℂ] E := realPart T
  let B : E →L[ℂ] E := imaginaryPart T
  have hA : (A : Module.End ℂ (E)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (selfAdjoint.isSelfAdjoint (x := realPart T))
  have hB : (B : Module.End ℂ (E)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (selfAdjoint.isSelfAdjoint (x := imaginaryPart T))
  have hAB : Commute A B := by
    letI : IsScalarTower ℂ
        (E →L[ℂ] E)
        (E →L[ℂ] E) :=
      { smul_assoc := by
          intro c S U
          apply ContinuousLinearMap.ext
          intro v
          change c • S (U v) = c • S (U v)
          rfl }
    letI : SMulCommClass ℂ
        (E →L[ℂ] E)
        (E →L[ℂ] E) :=
      { smul_comm := by
          intro c S U
          apply ContinuousLinearMap.ext
          intro v
          change c • S (U v) = S (c • U v)
          exact (S.map_smul c (U v)).symm }
    exact isStarNormal_iff_commute_realPart_imaginaryPart.mp hT
  exact ⟨A, B, hA, hB, hAB, (realPart_add_I_smul_imaginaryPart T).symm⟩

/-- Assemble normal eigenvectors over an abstract space before specializing its instances. -/
private lemma normal_eigenbasis_of_joint_solver {E : Type*} {ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    (hjoint : ∀ A B : Module.End ℂ E,
      A.IsSymmetric → B.IsSymmetric → Commute A B →
      ∃ b : OrthonormalBasis ι ℂ E, ∃ α β : ι → ℂ,
        ∀ i, A (b i) = α i • b i ∧ B (b i) = β i • b i)
    (T : E →L[ℂ] E) (hT : IsStarNormal T) :
    ∃ b : OrthonormalBasis ι ℂ E, ∃ z : ι → ℂ,
      ∀ i, T (b i) = z i • b i := by
  obtain ⟨A, B, hA, hB, hAB, hparts⟩ := normal_operator_parts T hT
  have hlin : Commute (A : Module.End ℂ (E))
      (B : Module.End ℂ (E)) := by
    exact congrArg (fun S : E →L[ℂ] E =>
      (S : Module.End ℂ (E))) hAB.eq
  obtain ⟨b, α, β, hb⟩ := hjoint (A : Module.End ℂ E) (B : Module.End ℂ E) hA hB hlin
  refine ⟨b, fun i => α i + Complex.I * β i, ?_⟩
  intro i
  have ha : A (b i) = α i • b i := (hb i).1
  have hb' : B (b i) = β i • b i := (hb i).2
  calc
    T (b i) = (A + Complex.I • B) (b i) :=
      congrArg (fun S : E →L[ℂ] E => S (b i))
        hparts
    _ = (α i + Complex.I * β i) • b i := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ha, hb', smul_smul, add_smul]

lemma normal_operator_eigenbasis {n : ℕ}
    (T : CVector (Fin n) →L[ℂ] CVector (Fin n)) (hT : IsStarNormal T) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)), ∃ z : Fin n → ℂ,
      ∀ i, T (b i) = z i • b i := by
  exact normal_eigenbasis_of_joint_solver
    (E := CVector (Fin n)) (ι := Fin n)
    (fun A B hA hB hAB => commuting_symmetric_eigenbasis A B hA hB hAB) T hT

theorem normal_unitary_diagonalization {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : X.conjTranspose * X = X * X.conjTranspose) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ z : Fin n → ℂ,
      X = (U : Square n) * Matrix.diagonal z * (U : Square n).conjTranspose := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X
  have hT : IsStarNormal T := by
    letI : IsStarNormal X := ⟨by
      change X.conjTranspose * X = X * X.conjTranspose
      exact hX⟩
    exact IsStarNormal.map
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) X
  obtain ⟨b, z, hb⟩ := normal_operator_eigenbasis T hT
  let U := basisUnitary b
  have hcolumns : X * (U : Square n) = (U : Square n) * Matrix.diagonal z := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [U, basisUnitary_entry]
    have h := congrArg (fun v : CVector (Fin n) => v i) (hb j)
    change (∑ k, X i k * b j k) = z j * b j i at h
    simpa only [mul_comm] using h
  have hU : (U : Square n) * (U : Square n).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  refine ⟨U, z, ?_⟩
  calc
    X = X * ((U : Square n) * (U : Square n).conjTranspose) := by
      rw [hU, mul_one]
    _ = (X * (U : Square n)) * (U : Square n).conjTranspose := by
      rw [Matrix.mul_assoc]
    _ = (U : Square n) * Matrix.diagonal z * (U : Square n).conjTranspose := by
      rw [hcolumns]

#print axioms normal_unitary_diagonalization
#assert_trust kernel normal_unitary_diagonalization

end NLA.MI04
