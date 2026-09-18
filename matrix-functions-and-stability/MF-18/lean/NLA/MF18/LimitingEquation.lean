/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Only the given one-sided limit and nonsingularity of X0 are used.
The explicit positive sequence transfers the previously proved closed-disk
stability theorem without assuming any continuous choice of eigenvectors.
-/
import NLA.MF18.ComplementaryStability
import NLA.MF18.StabilityLimits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
open scoped Topology

noncomputable section
namespace NLA.MF18

theorem limiting_equation_and_spectra {n : ℕ} [NeZero n] (C D R P : Mat n)
    (X : ℝ → Mat n) (X₀ : Mat n) (h : GreenAssumptions C D R P X X₀) :
    X₀ + C.conjTranspose * X₀⁻¹ * C = R ∧
    WeakStable (X₀⁻¹ * C) ∧ WeakStable (C.conjTranspose * X₀⁻¹) := by
  rcases h with ⟨hR, hP, hpos, hstab, hXlim, hXdet, _, _⟩
  let η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hηpos : ∀ k, 0 < η k := by
    intro k
    exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one)
  have hηlim : Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hηright : Filter.Tendsto η Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hηlim, Filter.Eventually.of_forall hηpos⟩
  have hx : Filter.Tendsto (fun k => X (η k)) Filter.atTop (nhds X₀) := hXlim.comp hηright
  have hinv_cont : ContinuousAt (fun Y : Mat n => Y⁻¹) X₀ :=
    continuousAt_matrix_inv X₀ (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hXdet))
  have hxi : Filter.Tendsto (fun k => (X (η k))⁻¹) Filter.atTop (nhds X₀⁻¹) :=
    hinv_cont.tendsto.comp hx
  have hiη : Filter.Tendsto (fun k => Complex.I * (η k : ℂ)) Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Complex.I)).mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hηlim)
  have hA : Filter.Tendsto (fun k => regularizedA C D (η k)) Filter.atTop (nhds C) := by
    simpa only [regularizedA, zero_smul, add_zero] using
      (tendsto_const_nhds (x := C)).add (hiη.smul (tendsto_const_nhds (x := D)))
  have hB : Filter.Tendsto (fun k => regularizedB C D (η k)) Filter.atTop
      (nhds C.conjTranspose) := by
    simpa only [regularizedB, zero_smul, add_zero] using
      (tendsto_const_nhds (x := C.conjTranspose)).add
        (hiη.smul (tendsto_const_nhds (x := D.conjTranspose)))
  have hQ : Filter.Tendsto (fun k => regularizedQ R P (η k)) Filter.atTop (nhds R) := by
    simpa only [regularizedQ, zero_smul, add_zero] using
      (tendsto_const_nhds (x := R)).add (hiη.smul (tendsto_const_nhds (x := P)))
  have heq : X₀ + C.conjTranspose * X₀⁻¹ * C = R := by
    have heq_lim : Filter.Tendsto (fun k => regularizedQ R P (η k)) Filter.atTop
        (nhds (X₀ + C.conjTranspose * X₀⁻¹ * C)) :=
      (hx.add ((hB.mul hxi).mul hA)).congr'
        (Filter.Eventually.of_forall fun k => (hstab (η k) (hηpos k)).2.1)
    exact tendsto_nhds_unique heq_lim hQ
  refine ⟨heq, ?_, ?_⟩
  · exact closed_disk_stability_limit (fun k => (X (η k))⁻¹ * regularizedA C D (η k))
      (X₀⁻¹ * C) (hxi.mul hA) (fun k => (hstab (η k) (hηpos k)).2.2)
  · exact closed_disk_stability_limit (fun k => regularizedB C D (η k) * (X (η k))⁻¹)
      (C.conjTranspose * X₀⁻¹) (hB.mul hxi)
      (fun k => complementary_stability C D R P hR hP hpos (η k) (hηpos k)
        (X (η k)) (hstab (η k) (hηpos k)))

#print axioms limiting_equation_and_spectra

end NLA.MF18
