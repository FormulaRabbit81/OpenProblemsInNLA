/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Definitions
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Separation.Basic

noncomputable section
namespace NLA.SP04

/-- An ambient open box has infinite sides, so polynomial uniqueness applies in all nine entries. -/
lemma polynomial_avoids_open (S : Set (Mat 3)) (hS : IsOpen S) (hne : S.Nonempty)
    (p : MvPolynomial (Fin 3 × Fin 3) ℝ) (hp : p ≠ 0) :
    ∃ U ∈ S, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ U ∈ S, MvPolynomial.eval (fun ij => U ij.1 ij.2) p = 0 := by
    intro U hU
    by_contra hval
    exact hn ⟨U, hU, hval⟩
  let e : (Fin 3 × Fin 3 → ℝ) ≃ₜ Mat 3 := Homeomorph.piCurry
  let T : Set (Fin 3 × Fin 3 → ℝ) := e ⁻¹' S
  have hT : IsOpen T := hS.preimage e.continuous
  obtain ⟨U, hU⟩ := hne
  have hx : e.symm U ∈ T := by simpa [T] using hU
  obtain ⟨s, hs, hsub⟩ := isOpen_pi_iff'.mp hT (e.symm U) hx
  apply hp
  apply MvPolynomial.funext_set s (fun i =>
    infinite_of_mem_nhds (e.symm U i) ((hs i).1.mem_nhds (hs i).2))
  intro y hy
  have hval := hzero (e y) (hsub hy)
  change MvPolynomial.eval y p = 0 at hval
  simpa using hval

end NLA.SP04
