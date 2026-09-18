/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

A compact set on which some continuous test is positive at each point admits
a finite family of tests and one positive lower threshold. The proof takes a
finite subcover of strictly positive threshold neighborhoods, then their
finite minimum. No boundedness or uniform positivity is an input assumption.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06

lemma compact_uniform_positive_tests {X I : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (hneK : K.Nonempty) (f : I → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hpos : ∀ x ∈ K, ∃ i, 0 < f i x) :
    ∃ s : Finset I, s.Nonempty ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ K, ∃ i ∈ s, c ≤ f i x := by
  classical
  let J := I × {c : ℝ // 0 < c}
  let U : J → Set X := fun j => {x | j.2.val < f j.1 x}
  have hopen (j : J) : IsOpen (U j) := isOpen_lt continuous_const (hf j.1)
  have hcover : K ⊆ ⋃ j : J, U j := by
    intro x hx
    obtain ⟨i, hi⟩ := hpos x hx
    refine Set.mem_iUnion.mpr ⟨(i, ⟨f i x / 2, half_pos hi⟩), ?_⟩
    change f i x / 2 < f i x
    linarith only [hi]
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hopen hcover
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hneK
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hjs, _⟩ := Set.mem_iUnion.mp hj
    exact ⟨j, hjs⟩
  let c : ℝ := s.inf' hsne (fun j => j.2.val)
  have hc : 0 < c := (Finset.lt_inf'_iff hsne).mpr (fun j _ => j.2.property)
  refine ⟨s.image Prod.fst, ?_, c, hc, ?_⟩
  · obtain ⟨j, hj⟩ := hsne
    exact ⟨j.1, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hjs, hjx⟩ := Set.mem_iUnion.mp hj
    have hcj : c ≤ j.2.val := Finset.inf'_le _ hjs
    have hjf : j.2.val < f j.1 x := hjx
    exact ⟨j.1, Finset.mem_image.mpr ⟨j, hjs, rfl⟩, hcj.trans hjf.le⟩

#print axioms compact_uniform_positive_tests
#assert_trust kernel compact_uniform_positive_tests

end NLA.MF06
