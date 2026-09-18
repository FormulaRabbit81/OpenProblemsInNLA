/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Generic images of actual chronological matrix words. The preimage construction
retains the original letters and their order; the map need not be injective.
Bundled monoid homomorphisms then preserve the literal matrix product.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma word_image_in {m n : ℕ} (M : Set (Square m)) (f : Square m → Square n)
    (w : List (Square m)) (hw : WordIn M w) : WordIn (f '' M) (w.map f) := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact ⟨A, hw A hA, rfl⟩

lemma word_image_preimage {m n : ℕ} (M : Set (Square m)) (f : Square m → Square n)
    (w : List (Square n)) (hw : WordIn (f '' M) w) :
    ∃ v : List (Square m), WordIn M v ∧ w = v.map f := by
  induction w with
  | nil => exact ⟨[], WordIn_nil M, rfl⟩
  | cons A w ih =>
      obtain ⟨hA, htail⟩ := (WordIn_cons_iff (f '' M) A w).mp hw
      obtain ⟨B, hB, rfl⟩ := hA
      obtain ⟨v, hv, rfl⟩ := ih htail
      exact ⟨B :: v, (WordIn_cons_iff M B v).mpr ⟨hB, hv⟩, rfl⟩

lemma matrixProduct_map_monoidHom {m n : ℕ} (f : Square m →* Square n)
    (w : List (Square m)) : matrixProduct (w.map f) = f (matrixProduct w) := by
  induction w with
  | nil => simp only [List.map_nil, matrixProduct_nil, map_one]
  | cons A w ih => simp only [List.map_cons, matrixProduct_cons, ih, map_mul]

#print axioms word_image_preimage
#assert_trust kernel word_image_preimage
#print axioms matrixProduct_map_monoidHom
#assert_trust kernel matrixProduct_map_monoidHom

end NLA.MF06
