/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
open Matrix
namespace NLA.PF02

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev FactorTuple (p q k : ℕ) := (Fin p → Mat k k) × (Fin q → Mat k k)

/-- Every row and column factor is genuinely real positive semidefinite. -/
def IsFactorization {p q k : ℕ} (M : Mat p q) (F : FactorTuple p q k) : Prop :=
  (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧
    ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j

/-- The full factorization space with its inherited finite-dimensional Euclidean topology. -/
abbrev Factorization {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  {F : FactorTuple p q k // IsFactorization M F}

/-- The actual minimum among all positive integer factor sizes, including attainment. -/
def IsPSDRank {p q : ℕ} (M : Mat p q) (k : ℕ) : Prop :=
  IsLeast {ℓ : ℕ | 1 ≤ ℓ ∧ Nonempty (Factorization M ℓ)} k

/-- A single genuine invertible change of basis, on all row and column factors. -/
def Congruent {p q k : ℕ} {M : Mat p q} (F G : Factorization M k) : Prop :=
  ∃ S : (Mat k k)ˣ,
    (∀ i, G.val.1 i = (↑S : Mat k k).transpose * F.val.1 i * ↑S) ∧
    (∀ j, G.val.2 j = (↑(S⁻¹) : Mat k k) * F.val.2 j * (↑(S⁻¹) : Mat k k).transpose)

/-- Quotient topology on actual congruence orbits; the public orbit theorem checks exact equality. -/
abbrev OrbitSpace {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  Quot (@Congruent p q k M)

def AllMinimalOrbitsConnected : Prop :=
  ∀ (k p q : ℕ), 3 ≤ k → 1 ≤ p → 1 ≤ q → ∀ M : Mat p q,
    (∀ i j, 0 ≤ M i j) → M.rank = k * (k + 1) / 2 → IsPSDRank M k →
    IsConnected (Set.univ : Set (OrbitSpace M k))

/-- Fixed diagonal/off-diagonal coordinates on all real three-by-three matrices. -/
def coord (X : Mat 3 3) : Fin 6 → ℝ :=
  ![X 0 0, X 1 1, X 2 2, X 0 1, X 0 2, X 1 2]

def rowCoordinates (A : Fin 6 → Mat 3 3) : Mat 6 6 := fun i => coord (A i)

def orientationDet {M : Mat 6 6} (F : Factorization M 3) : ℝ :=
  (rowCoordinates F.val.1).det

def witnessM : Mat 6 6 := !![
  24,20,20,16,16,16;
  20,24,20,16,16,16;
  20,20,24,16,16,16;
  16,16,16,14,12,12;
  16,16,16,12,14,12;
  16,16,16,12,12,14]

/-- The sign parameter is used only at +1 and −1 in the two explicit tuples. -/
def witnessFactors (s : ℝ) : Fin 6 → Mat 3 3 := ![
  !![4,0,0; 0,2,0; 0,0,2],
  !![2,0,0; 0,4,0; 0,0,2],
  !![2,0,0; 0,2,0; 0,0,4],
  !![2,s,0; s,2,0; 0,0,2],
  !![2,0,1; 0,2,0; 1,0,2],
  !![2,0,0; 0,2,1; 0,1,2]]

def witnessTuple (s : ℝ) : FactorTuple 6 6 3 := (witnessFactors s, witnessFactors s)

end NLA.PF02
