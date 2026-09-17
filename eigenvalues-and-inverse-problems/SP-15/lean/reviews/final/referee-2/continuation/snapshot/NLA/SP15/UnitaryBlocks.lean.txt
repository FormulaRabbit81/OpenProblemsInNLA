/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

An arbitrary original one-sided unitary intertwiner is forced to be block
diagonal. The lower blocks vanish by root-unit cancellation in A_x U=U A_y;
the upper blocks then vanish by the actual unitary block equations.
-/
import NLA.SP15.TripleBlocks
import NLA.SP15.SquareRoots
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix

theorem unitary_intertwiner_blocks (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox) (U : Square 9)
    (hU : U.conjTranspose * U = 1)
    (hA : constructedMatrix y = U.conjTranspose * constructedMatrix x * U) :
    ∃ U₁ U₂ U₃ : Square 3,
      U₁.conjTranspose * U₁ = 1 ∧ U₂.conjTranspose * U₂ = 1 ∧
      U₃.conjTranspose * U₃ = 1 ∧ U = diagonalBlocks U₁ U₂ U₃ ∧
      pRoot y = U₁.conjTranspose * pRoot x * U₂ ∧
      qRoot y = U₂.conjTranspose * qRoot x * U₃ := by
  have hUU : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hinter : constructedMatrix x * U = U * constructedMatrix y := by
    rw [hA]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  let reidx := Matrix.reindexAlgEquiv ℂ ℂ blockEquiv.symm
  let V : BlockSquare := reidx U
  have hconstructed (w : Parameters) : reidx (constructedMatrix w) = blockMatrix w := by
    -- Expose the construction and inverse reindexing as the same equivalence pair.
    change (Matrix.reindex blockEquiv blockEquiv).symm
      ((Matrix.reindex blockEquiv blockEquiv) (blockMatrix w)) = blockMatrix w
    exact (Matrix.reindex blockEquiv blockEquiv).symm_apply_apply (blockMatrix w)
  have hstar : reidx U.conjTranspose = (reidx U).conjTranspose :=
    (Matrix.conjTranspose_reindex blockEquiv.symm blockEquiv.symm U).symm
  have hV : V.conjTranspose * V = 1 := by
    have hv := congrArg reidx hU
    rw [map_mul, map_one, hstar] at hv
    exact hv
  have hVA : blockMatrix x * V = V * blockMatrix y := by
    have hi := congrArg reidx hinter
    rw [map_mul, map_mul, hconstructed, hconstructed] at hi
    exact hi
  let a : Square 3 := V.submatrix Sum.inl Sum.inl
  let b : Square 3 := V.submatrix Sum.inl (Sum.inr ∘ Sum.inl)
  let c : Square 3 := V.submatrix Sum.inl (Sum.inr ∘ Sum.inr)
  let d : Square 3 := V.submatrix (Sum.inr ∘ Sum.inl) Sum.inl
  let e : Square 3 := V.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
  let f : Square 3 := V.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr)
  let g : Square 3 := V.submatrix (Sum.inr ∘ Sum.inr) Sum.inl
  let h : Square 3 := V.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inl)
  let k : Square 3 := V.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inr)
  have hform : V = tripleBlock a b c d e f g h k := triple_decomposition V
  have hnil (w : Parameters) : blockMatrix w =
      tripleBlock 0 (pRoot w) 0 0 0 (qRoot w) 0 0 0 := rfl
  have hentries := hVA
  rw [hnil x, hnil y, hform, triple_mul, triple_mul, triple_eq_iff] at hentries
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hentries
  obtain ⟨h21, ⟨h12, _⟩, ⟨h31, _⟩, h32, h23, _, _⟩ := hentries
  have hroot := square_root_semantics x hx
  have hd : d = 0 := hroot.2.2.2.2.1.mul_left_cancel (by simpa only [Matrix.mul_zero] using h21)
  have hg : g = 0 := hroot.2.2.2.2.2.mul_left_cancel (by simpa only [Matrix.mul_zero] using h31)
  have hh : h = 0 := by
    rw [hd, Matrix.zero_mul] at h32
    exact hroot.2.2.2.2.2.mul_left_cancel (by simpa only [Matrix.mul_zero] using h32)
  have hupper : V = tripleBlock a b c 0 e f 0 0 k := by
    simpa only [hd, hg, hh] using hform
  have hblocks := hV
  rw [hupper, triple_conjTranspose, triple_mul, ← triple_one, triple_eq_iff] at hblocks
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    add_zero] at hblocks
  obtain ⟨haa, ⟨hab, hac⟩, _, hee, hef, _, hkk⟩ := hblocks
  have hau : IsUnit a.conjTranspose := isUnit_iff_exists_inv.mpr ⟨a, haa⟩
  have hb : b = 0 := hau.mul_left_cancel (by simpa only [Matrix.mul_zero] using hab)
  have hc : c = 0 := hau.mul_left_cancel (by simpa only [Matrix.mul_zero] using hac)
  have hee' : e.conjTranspose * e = 1 := by
    simpa only [hb, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] using hee
  have heu : IsUnit e.conjTranspose := isUnit_iff_exists_inv.mpr ⟨e, hee'⟩
  have hf : f = 0 := by
    simp only [hb, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] at hef
    exact heu.mul_left_cancel (by simpa only [Matrix.mul_zero] using hef)
  have hkk' : k.conjTranspose * k = 1 := by
    simpa only [hc, hf, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] using hkk
  have hdiag : V = tripleBlock a 0 0 0 e 0 0 0 k := by
    simpa only [hb, hc, hf] using hupper
  have hR : pRoot y = a.conjTranspose * pRoot x * e := by
    have hr := congrArg (fun M : Square 3 => a.conjTranspose * M) h12
    simpa only [← Matrix.mul_assoc, haa, Matrix.one_mul] using hr.symm
  have hS : qRoot y = e.conjTranspose * qRoot x * k := by
    have hs := congrArg (fun M : Square 3 => e.conjTranspose * M) h23
    simpa only [← Matrix.mul_assoc, hee', Matrix.one_mul] using hs.symm
  refine ⟨a, e, k, haa, hee', hkk', ?_, hR, hS⟩
  -- The frozen diagonalBlocks is this reindexed block diagonal matrix; return to original indices.
  change U = Matrix.reindex blockEquiv blockEquiv (tripleBlock a 0 0 0 e 0 0 0 k)
  rw [← hdiag]
  exact ((Matrix.reindex blockEquiv blockEquiv).apply_symm_apply U).symm

#print axioms unitary_intertwiner_blocks
#assert_trust kernel unitary_intertwiner_blocks

end
end NLA.SP15
