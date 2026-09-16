/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.CongruencePolynomial
import NLA.PF02.Orbits
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section
open Matrix Set Filter
open scoped Topology
namespace NLA.PF02

lemma all_orientation_nonzero (F : Factorization witnessM 3) : orientationDet F ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det (factorization_coordinate_identity F)
  change (rowCoordinates F.val.1).det = 0 at hz
  rw [Matrix.det_mul, Matrix.det_mul, hz, zero_mul, zero_mul, witness_matrix_det] at h
  norm_num at h

lemma continuous_orientationDet : Continuous (orientationDet (M := witnessM)) := by
  unfold orientationDet rowCoordinates coord
  fun_prop

def fiberSign (F : Factorization witnessM 3) : Bool := decide (0 < orientationDet F)

lemma continuous_fiberSign : Continuous fiberSign := by
  apply continuous_iff_continuousAt.mpr
  intro F
  by_cases hp : 0 < orientationDet F
  · have he : ∀ᶠ G in 𝓝 F, 0 < orientationDet G :=
      (isOpen_lt continuous_const continuous_orientationDet).mem_nhds hp
    apply (continuousAt_const (y := true)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [fiberSign, hG])
  · have hn : orientationDet F < 0 := lt_of_le_of_ne (le_of_not_gt hp) (all_orientation_nonzero F)
    have he : ∀ᶠ G in 𝓝 F, orientationDet G < 0 :=
      (isOpen_lt continuous_orientationDet continuous_const).mem_nhds hn
    apply (continuousAt_const (y := false)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [fiberSign, not_lt_of_gt hG])

lemma fiberSign_congruent (F G : Factorization witnessM 3) (h : Congruent F G) :
    fiberSign F = fiberSign G := by
  unfold fiberSign
  simp only [orientation_congruent F G h]

def orbitSign : OrbitSpace witnessM 3 → Bool := Quot.lift fiberSign fiberSign_congruent

lemma continuous_orbitSign : Continuous orbitSign :=
  continuous_quot_lift fiberSign_congruent continuous_fiberSign

lemma orbitSign_surjective : Function.Surjective orbitSign := by
  let Fplus : Factorization witnessM 3 := ⟨witnessTuple 1, explicit_factorizations.1⟩
  let Fminus : Factorization witnessM 3 := ⟨witnessTuple (-1), explicit_factorizations.2.1⟩
  have hp : orientationDet Fplus = 32 := witness_numeric_data.2.2.2.1
  have hn : orientationDet Fminus = -32 := witness_numeric_data.2.2.2.2
  intro b
  cases b
  · refine ⟨Quot.mk _ Fminus, ?_⟩
    change decide (0 < orientationDet Fminus) = false
    rw [hn]
    exact decide_eq_false (by linarith [thirty_two_pos])
  · refine ⟨Quot.mk _ Fplus, ?_⟩
    change decide (0 < orientationDet Fplus) = true
    rw [hp]
    exact decide_eq_true thirty_two_pos

lemma orbit_quotient_disconnected :
    ¬ IsConnected (Set.univ : Set (OrbitSpace witnessM 3)) := by
  intro h
  have hi := (h.image orbitSign continuous_orbitSign.continuousOn).isPreconnected.subsingleton
  obtain ⟨F, hF⟩ := orbitSign_surjective false
  obtain ⟨G, hG⟩ := orbitSign_surjective true
  have hbad : false = true := hi ⟨F, Set.mem_univ _, hF⟩ ⟨G, Set.mem_univ _, hG⟩
  cases hbad

#assert_trust kernel all_orientation_nonzero
#assert_trust kernel orbitSign_surjective
#assert_trust kernel orbit_quotient_disconnected
#print axioms orbit_quotient_disconnected

end NLA.PF02
