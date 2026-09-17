/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The same middle block conjugates P and Q. The first identity uses RᴴR;
the second uses SSᴴ, with their respective outer unitary blocks canceled.
-/
import NLA.SP15.UnitaryBlocks

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix

theorem middle_block_conjugacy (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox)
    (h : UnitarySimilar (constructedMatrix x) (constructedMatrix y)) :
    ∃ V : Square 3, V.conjTranspose * V = 1 ∧
      pMatrix y = V.conjTranspose * pMatrix x * V ∧
      qMatrix y = V.conjTranspose * qMatrix x * V := by
  obtain ⟨U, hU, hA⟩ := h
  obtain ⟨U₁, U₂, U₃, h₁, h₂, h₃, _, hR, hS⟩ :=
    unitary_intertwiner_blocks x y hx hy U hU hA
  have h₁' : U₁ * U₁.conjTranspose = 1 := mul_eq_one_comm.mp h₁
  have h₃' : U₃ * U₃.conjTranspose = 1 := mul_eq_one_comm.mp h₃
  have rx := square_root_semantics x hx
  have ry := square_root_semantics y hy
  have hPx : (pRoot x).conjTranspose * pRoot x = pMatrix x := by
    rw [rx.1.eq, rx.2.2.1]
  have hPy : (pRoot y).conjTranspose * pRoot y = pMatrix y := by
    rw [ry.1.eq, ry.2.2.1]
  have hQx : qRoot x * (qRoot x).conjTranspose = qMatrix x := by
    rw [rx.2.1.eq, rx.2.2.2.1]
  have hQy : qRoot y * (qRoot y).conjTranspose = qMatrix y := by
    rw [ry.2.1.eq, ry.2.2.2.1]
  refine ⟨U₂, h₂, ?_, ?_⟩
  · calc
      pMatrix y = (pRoot y).conjTranspose * pRoot y := hPy.symm
      _ = (U₁.conjTranspose * pRoot x * U₂).conjTranspose *
          (U₁.conjTranspose * pRoot x * U₂) := by rw [hR]
      _ = U₂.conjTranspose *
          ((pRoot x).conjTranspose * (U₁ * U₁.conjTranspose) * pRoot x) * U₂ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = U₂.conjTranspose * pMatrix x * U₂ := by
        rw [h₁', Matrix.mul_one, hPx]
  · calc
      qMatrix y = qRoot y * (qRoot y).conjTranspose := hQy.symm
      _ = (U₂.conjTranspose * qRoot x * U₃) *
          (U₂.conjTranspose * qRoot x * U₃).conjTranspose := by rw [hS]
      _ = U₂.conjTranspose *
          (qRoot x * (U₃ * U₃.conjTranspose) * (qRoot x).conjTranspose) * U₂ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = U₂.conjTranspose * qMatrix x * U₂ := by
        rw [h₃', Matrix.mul_one, hQx]

#print axioms middle_block_conjugacy
#assert_trust kernel middle_block_conjugacy

end
end NLA.SP15
