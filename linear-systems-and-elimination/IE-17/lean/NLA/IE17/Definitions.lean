/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open Matrix
namespace NLA.IE17

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The induced Euclidean operator norm, with both spaces carrying their L2 norms. -/
def spectralNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def residual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec m :=
  b - A.toEuclideanLin x

def normalResidual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec n :=
  A.transpose.toEuclideanLin (residual A b x)

/-- Only the matrix is perturbed; b is kept fixed. -/
def Feasible {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (E : Mat m n) : Prop :=
  normalResidual (A + E) b x = 0

def errorSet {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Set ℝ :=
  {δ | ∃ E : Mat m n, Feasible A b x E ∧ spectralNorm E = δ}

/-- A minimum, including actual attainment, not merely an infimum. -/
def IsOptimalError {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (δ : ℝ) : Prop :=
  IsLeast (errorSet A b x) δ

/-- K_k(AᵀA,Aᵀb), with K_0={0}. -/
def krylov {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ {v | ∃ j : ℕ, j < k ∧
    v = ((A.transpose * A) ^ j).toEuclideanLin (A.transpose.toEuclideanLin b)}

/-- Exact normal-residual minimization and the specified minimum-length convention. -/
def IsLSMRIterate {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) (x : Vec n) : Prop :=
  x ∈ krylov A b k ∧
  (∀ y ∈ krylov A b k, ‖normalResidual A b x‖ ≤ ‖normalResidual A b y‖) ∧
  (∀ y ∈ krylov A b k, ‖normalResidual A b y‖ = ‖normalResidual A b x‖ → ‖x‖ ≤ ‖y‖)

/-- A complete finite exact run from zero through its first least-squares solution. -/
def IsTerminatingLSMRRun {m n N : ℕ} (A : Mat m n) (b : Vec m)
    (xs : Fin (N + 1) → Vec n) : Prop :=
  xs 0 = 0 ∧ (∀ k, IsLSMRIterate A b k.val (xs k)) ∧
  (∀ k, k.val < N → normalResidual A b (xs k) ≠ 0) ∧
  normalResidual A b (xs (Fin.last N)) = 0

/-- Four real Moore–Penrose equations; no nonsingular-inverse substitute. -/
def IsMoorePenrose {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : Matrix ι κ ℝ) (P : Matrix κ ι ℝ) : Prop :=
  K * P * K = K ∧ P * K * P = P ∧ (K * P).transpose = K * P ∧
    (P * K).transpose = P * K

/-- The canonical stacked matrix [A; (‖r‖₂/‖x‖₂)I]. -/
def stacked {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ :=
  fun i j => match i with
    | Sum.inl i => A i j
    | Sum.inr i => if i = j then ‖residual A b x‖ / ‖x‖ else 0

def stackedResidual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    EuclideanSpace ℝ (Fin m ⊕ Fin n) :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl i => residual A b x i
    | Sum.inr _ => 0)

/-- The canonical approximation on nonzero iterates, with its exact-LS zero convention.
The complete target also requires uniqueness, so no choice of generalized inverse changes q. -/
def IsApproximation {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (q : ℝ) : Prop :=
  x ≠ 0 ∧ if normalResidual A b x = 0 then q = 0 else
    ∃ P : Matrix (Fin n) (Fin m ⊕ Fin n) ℝ,
      IsMoorePenrose (stacked A b x) P ∧
      q = ‖((stacked A b x) * P).toEuclideanLin (stackedResidual A b x)‖ / ‖x‖

def witnessA : Mat 4 3 := !![1, 0, 0; 0, 6, 0; 0, 0, 5; 0, 0, 0]
def witnessB : Vec 4 := WithLp.toLp 2 ![11, 1, 1, 1]
def witnessX₁ : Vec 3 := WithLp.toLp 2 ![(11231 : ℝ) / 31201, 6126 / 31201, 5105 / 31201]
def witnessX₂ : Vec 3 := WithLp.toLp 2 ![(87659 : ℝ) / 55219, 7599 / 55219, 16865 / 55219]
def witnessX₃ : Vec 3 := WithLp.toLp 2 ![11, (1 : ℝ) / 6, (1 : ℝ) / 5]
def witnessRun : Fin 4 → Vec 3 := ![0, witnessX₁, witnessX₂, witnessX₃]

/-- The first original conjecture, on successive nonzero iterates through exact termination. -/
def OptimalErrorsNonincreasing : Prop :=
  ∀ (m n N : ℕ) (A : Mat m n) (b : Vec m) (xs : Fin (N + 1) → Vec n),
    IsTerminatingLSMRRun A b xs →
    ∀ (i j : Fin (N + 1)), j.val = i.val + 1 → xs i ≠ 0 → xs j ≠ 0 →
    ∀ (μ ν : ℝ), IsOptimalError A b (xs i) μ → IsOptimalError A b (xs j) ν → ν ≤ μ

/-- The second original conjecture for the specified Moore–Penrose approximation. -/
def ApproximationErrorsNonincreasing : Prop :=
  ∀ (m n N : ℕ) (A : Mat m n) (b : Vec m) (xs : Fin (N + 1) → Vec n),
    IsTerminatingLSMRRun A b xs →
    ∀ (i j : Fin (N + 1)), j.val = i.val + 1 → xs i ≠ 0 → xs j ≠ 0 →
    ∀ (μ ν : ℝ), IsApproximation A b (xs i) μ → IsApproximation A b (xs j) ν → ν ≤ μ

end NLA.IE17
