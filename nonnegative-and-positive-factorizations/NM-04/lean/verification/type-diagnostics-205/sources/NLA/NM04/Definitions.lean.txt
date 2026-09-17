/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. The original coefficient identity is due
to Rowland and Wu; the complete mathematical solution followed here is
Matthew J. Colbrook's NM-04 manuscript, Theorem 1, Sections 1–4.

Concrete statement definitions only. No matrix-scaling existence, uniqueness,
minor identity, derivative, minimizer, or polynomial root is assumed here.
All matrix dimensions and minor cardinalities remain arbitrary.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

universe u v w
variable {α : Type u} {β : Type v} {𝕜 : Type w}

/-- A pair of actual finite subsets with equal cardinalities. -/
abbrev MinorIndex (α : Type u) (β : Type v) :=
  {RC : Finset α × Finset β // RC.1.card = RC.2.card}

def emptyIndex (α : Type u) (β : Type v) : MinorIndex α β :=
  ⟨(∅, ∅), rfl⟩

/-- One-based position in the increasing order. Only member positions enter signs. -/
def position [LinearOrder α] (s : α) (U : Finset α) : ℕ :=
  (U.filter (fun t => t < s)).card + 1

/-- The two maps enumerate the selected rows and columns in increasing order. -/
def minorMatrix [LinearOrder α] [LinearOrder β]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    Matrix (Fin I.1.1.card) (Fin I.1.1.card) 𝕜 :=
  fun i j => T (I.1.1.orderEmbOfFin rfl i)
    (I.1.2.orderEmbOfFin I.property.symm j)

def minor [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) : 𝕜 :=
  (minorMatrix T I).det

/-- Deleting members preserves equality of the two selected cardinalities. -/
def erasedIndex [DecidableEq α] [DecidableEq β]
    (I : MinorIndex α β) (s : I.1.1) (t : I.1.2) : MinorIndex α β :=
  ⟨(I.1.1.erase s, I.1.2.erase t), by
    calc
      (I.1.1.erase s).card = I.1.1.card - 1 := Finset.card_erase_of_mem s.property
      _ = I.1.2.card - 1 := congrArg (fun k : ℕ => k - 1) I.property
      _ = (I.1.2.erase t).card := (Finset.card_erase_of_mem t.property).symm⟩

/-- The actual polynomial cofactor form, not an assumed derivative. -/
def cofactorForm [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (Z : Matrix α β 𝕜) : 𝕜 :=
  ∑ i : Fin I.1.1.card, ∑ j : Fin I.1.1.card,
    (minorMatrix T I).adjugate j i * minorMatrix Z I i j

/-- Literal singleton supports from the canonical four off-diagonal cases. -/
def RaisingSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s : α) (t : β) : Prop :=
  I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = {s} ∧
  I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = {t}

def LoweringSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s : α) (t : β) : Prop :=
  I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = ∅ ∧
  I.1.2 \ J.1.2 = {t} ∧ J.1.2 \ I.1.2 = ∅

def ColumnExchangeSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s t : β) : Prop :=
  I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = ∅ ∧
  I.1.2 \ J.1.2 = {s} ∧ J.1.2 \ I.1.2 = {t}

def RowExchangeSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s t : α) : Prop :=
  I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = {t} ∧
  I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = ∅

def raisingCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : β, if RaisingSupport I J s t then
    (-1) ^ (position s J.1.1 + position t J.1.2) else 0

def loweringCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : β, if LoweringSupport I J s t then
    (-1) ^ (position s I.1.1 + position t I.1.2) else 0

def columnExchangeCoefficient [Fintype β] [DecidableEq α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : β, ∑ t : β, if ColumnExchangeSupport I J s t then
    (-1) ^ (position s I.1.2 + position t J.1.2) else 0

def rowExchangeCoefficient [Fintype α] [LinearOrder α] [DecidableEq β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : α, if RowExchangeSupport I J s t then
    (-1) ^ (position s I.1.1 + position t J.1.1) else 0

def lowering [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) : 𝕜 :=
  ∑ J : MinorIndex α β, (loweringCoefficient I J : 𝕜) * f J

def raising [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) : 𝕜 :=
  ∑ J : MinorIndex α β, (raisingCoefficient I J : 𝕜) * f J

def columnExchange [Fintype α] [Fintype β] [DecidableEq α] [LinearOrder β]
    [CommRing 𝕜] (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) : 𝕜 :=
  ∑ J : MinorIndex α β, (columnExchangeCoefficient I J : 𝕜) * f J

def rowExchange [Fintype α] [Fintype β] [LinearOrder α] [DecidableEq β]
    [CommRing 𝕜] (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) : 𝕜 :=
  ∑ J : MinorIndex α β, (rowExchangeCoefficient I J : 𝕜) * f J

/-- Append the border as the last row and column, including the case `k=0`. -/
def borderedMatrix {k : ℕ} (V : Matrix (Fin k) (Fin k) 𝕜)
    (a b : Fin k → 𝕜) (d : 𝕜) : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜 :=
  Fin.snoc (fun i => Fin.snoc (V i) (b i)) (Fin.snoc a d)

abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Original labels 2,...,m, stored as their zero-based `Fin m` indices. -/
abbrev Tail (m : ℕ) := {i : Fin m // 0 < i.val}
abbrev Index (m n : ℕ) := MinorIndex (Tail m) (Tail n)

def firstIndex {m : ℕ} (hm : 1 ≤ m) : Fin m := ⟨0, hm⟩

def tailMatrix {m n : ℕ} (A : Rect m n) : Matrix (Tail m) (Tail n) ℝ :=
  fun i j => A i.val j.val

/-- First index followed by increasing tail indices is the source's increasing order. -/
def delta {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (I : Index m n) : ℝ :=
  Matrix.det (A.submatrix
    (Fin.cons (firstIndex hm) (fun i => (I.1.1.orderEmbOfFin rfl i).val))
    (Fin.cons (firstIndex hn) (fun j => (I.1.2.orderEmbOfFin I.property.symm j).val)))

def gamma {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (I : Index m n) : ℝ :=
  A (firstIndex hm) (firstIndex hn) * minor (tailMatrix A) I

/-- Integer arithmetic, including the negative diagonal and lowering coefficient. -/
def H (m n : ℕ) : Matrix (Index m n) (Index m n) ℤ :=
  fun I J => if I = J then
    (I.1.1.card : ℤ) * ((m : ℤ) + (n : ℤ)) - (m : ℤ) * (n : ℤ)
  else (m : ℤ) * raisingCoefficient I J - (n : ℤ) * loweringCoefficient I J +
    (m : ℤ) * columnExchangeCoefficient I J + (n : ℤ) * rowExchangeCoefficient I J

def HReal (m n : ℕ) : Matrix (Index m n) (Index m n) ℝ :=
  fun I J => (H m n I J : ℝ)

def pencil {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (z : ℝ) : Matrix (Index m n) (Index m n) ℝ :=
  Matrix.diagonal (gamma A hm hn) +
    (z / (m : ℝ)) • (HReal m n * Matrix.diagonal (delta A hm hn))

def weight (m n : ℕ) (I : Index m n) : ℝ :=
  ((n : ℝ) / (m : ℝ)) ^ I.1.1.card

def Positive {m n : ℕ} (A : Rect m n) : Prop := ∀ i j, 0 < A i j

def Balanced {m n : ℕ} (S : Rect m n) : Prop :=
  (∀ i, ∑ j, S i j = 1) ∧ (∀ j, ∑ i, S i j = (m : ℝ) / (n : ℝ))

/-- Entrywise form of multiplication by the actual two diagonal matrices. -/
def diagonalScale {m n : ℕ} (A : Rect m n) (a : Fin m → ℝ)
    (b : Fin n → ℝ) : Rect m n := fun i j => a i * A i j * b j

def ScaledBalanced {m n : ℕ} (A S : Rect m n) : Prop :=
  ∃ (a : Fin m → ℝ) (b : Fin n → ℝ),
    (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ S = diagonalScale A a b ∧ Balanced S

/-- Total choice only. Existence, uniqueness and exclusion of the fallback on
    positive inputs are separate contracts and are not assumptions of this definition. -/
def sinkhorn {m n : ℕ} (A : Rect m n) : Rect m n :=
  if h : ∃ S, ScaledBalanced A S then Classical.choose h else 0

def rowPartition {m n : ℕ} (A : Rect m n) (t : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * Real.exp (t j)

def potential {m n : ℕ} (A : Rect m n) (t : Fin n → ℝ) : ℝ :=
  (∑ i, Real.log (rowPartition A t i)) - ((m : ℝ) / (n : ℝ)) * ∑ j, t j

/-- Explicit candidate derivative data; its actual derivative identity is a contract. -/
def columnImbalance {m n : ℕ} (A : Rect m n) (t : Fin n → ℝ) (j : Fin n) : ℝ :=
  (∑ i, A i j * Real.exp (t j) / rowPartition A t i) - (m : ℝ) / (n : ℝ)

def meanZero (n : ℕ) : Set (Fin n → ℝ) := {t | ∑ j, t j = 0}

def rowNormalized {m n : ℕ} (A : Rect m n) (t : Fin n → ℝ) : Rect m n :=
  diagonalScale A (fun i => (rowPartition A t i)⁻¹) (fun j => Real.exp (t j))

/-- The only inverse in the minor argument is this distinguished scalar pivot. -/
def schurTail {m n : ℕ} (S : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Matrix (Tail m) (Tail n) ℝ :=
  fun i j => S i.val j.val -
    S i.val (firstIndex hn) * S (firstIndex hm) j.val /
      S (firstIndex hm) (firstIndex hn)

def covarianceFactor {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (I : Index m n) : ℝ :=
  a (firstIndex hm) * b (firstIndex hn) *
    (∏ i ∈ I.1.1, a i.val) * (∏ j ∈ I.1.2, b j.val)

end
end NLA.NM04
