import Mathlib

/- Statements-only draft. Mathematical proof: George Stepaniants, KE-05 solution
at deb549fa9ddd6b119e6c59016f268237e645dfa2. Original framework: Nian Shao.
Formalization draft: Sidney Holden with AI assistance. No proof is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace NLA.KE05

abbrev Mat (b : ℕ) := Matrix (Fin b) (Fin b) ℝ
abbrev Data (b d : ℕ) := Fin d → Fin b → ℝ
abbrev Sample (b d : ℕ) := (Fin d × Fin b × Fin b) → ℝ

/-- Every matrix entry is an independent real N(0,1) variable. -/
def gaussianLaw (b d : ℕ) : Measure (Sample b d) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def omega {b d : ℕ} (w : Sample b d) (i : Fin d) : Mat b :=
  fun r c => w (i, r, c)

def Admissible {b d : ℕ} (L : Data b d) : Prop :=
  ∀ i j : Fin d, i ≠ j → ∀ r s : Fin b, L i r ≠ L j s

/-- Literal order (k,0,...,k-1,k+1,...,d-1). getD is only queried at i<d. -/
def rootOrder {d : ℕ} (k i : Fin d) : Fin d :=
  (k :: (List.finRange d).erase k).getD i.val k

def baseBlock {b d : ℕ} (L : Data b d) (w : Sample b d) (k i : Fin d) : Mat b :=
  let j := rootOrder k i
  (omega w j)⁻¹ * Matrix.diagonal (L j) * omega w j

structure RecurrenceState (b d : ℕ) where
  hat : Fin d → Mat b
  lastS : Fin d → Mat b

/-- S_(i,j) from its literal ascending recursion, using the already computed hats. -/
def prefixS {b d : ℕ} (L : Data b d) (w : Sample b d) (k i : Fin d)
    (hats : Fin d → Mat b) (j : ℕ) : Mat b :=
  (((List.finRange d).drop (i.val + 1)).take (j - i.val)).foldl
    (fun S t => baseBlock L w k i * S - S * hats t) 1

def recurrenceStep {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d)
    (state : RecurrenceState b d) (i : Fin d) : RecurrenceState b d :=
  let S := prefixS L w k i state.hat (d - 1)
  let O := omega w (rootOrder k i) * S
  { hat := Function.update state.hat i (O⁻¹ * Matrix.diagonal (L (rootOrder k i)) * O)
    lastS := Function.update state.lastS i S }

/-- Descending i=d-1,...,0, exactly as specified in KE-05. -/
def recurrence {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d) :
    RecurrenceState b d :=
  (List.finRange d).reverse.foldl (recurrenceStep L w k) ⟨fun _ => 0, fun _ => 0⟩

def Valid {b d : ℕ} (L : Data b d) (w : Sample b d) : Prop :=
  (∀ i, (omega w i).det ≠ 0) ∧
  ∀ k i : Fin d,
    (omega w (rootOrder k i) * (recurrence L w k).lastS i).det ≠ 0

/-- Explicit Euclidean operator norm, independent of the entrywise matrix norm instance. -/
def spectralNorm {b : ℕ} (A : Mat b) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

def lowerEndpoint {b d : ℕ} (L : Data b d) : ℝ := sInf {x | ∃ i r, x = L i r}
def upperEndpoint {b d : ℕ} (L : Data b d) : ℝ := sSup {x | ∃ i r, x = L i r}

/-- The specified endpoint 0/0 convention; other ratios are ordinary real division. -/
def endpointRatio {b : ℕ} (t : ℝ) (H D : Mat b) : ℝ :=
  let numerator := spectralNorm (t • (1 : Mat b) - H)
  let denominator := spectralNorm (t • (1 : Mat b) - D)
  if numerator = 0 ∧ denominator = 0 then 1 else numerator / denominator

def monoOrdering {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d) : ℝ :=
  max 1 (sSup {x | ∃ i : Fin d, 1 ≤ i.val ∧
    (x = endpointRatio (lowerEndpoint L) ((recurrence L w k).hat i)
      (Matrix.diagonal (L (rootOrder k i))) ∨
     x = endpointRatio (upperEndpoint L) ((recurrence L w k).hat i)
      (Matrix.diagonal (L (rootOrder k i))))})

def crossGap {b d : ℕ} (L : Data b d) (k : Fin d) : ℝ :=
  sInf {x | ∃ i : Fin d, 1 ≤ i.val ∧ ∃ r s : Fin b,
    x = |L k r - L (rootOrder k i) s|}

def firstPosition {d : ℕ} (k : Fin d) : Fin d := ⟨0, Nat.zero_lt_of_lt k.isLt⟩

def coefOrdering {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d) : ℝ :=
  let S := (recurrence L w k).lastS (firstPosition k)
  Real.rpow (spectralNorm S⁻¹) (1 / ((d - 1 : ℕ) : ℝ)) * crossGap L k

def mono {b d : ℕ} (L : Data b d) (w : Sample b d) : ℝ :=
  sSup (Set.range (monoOrdering L w))
def coef {b d : ℕ} (L : Data b d) (w : Sample b d) : ℝ :=
  sSup (Set.range (coefOrdering L w))

/-- The literal constants when defined, zero on the null invalid event. -/
def totalConstant {b d : ℕ} (L : Data b d) (w : Sample b d) : ℝ :=
  if Valid L w then mono L w * coef L w else 0

def boundedProbability {b d : ℕ} (L : Data b d) (C : ℝ) : ℝ :=
  ((gaussianLaw b d) {w | totalConstant L w ≤ C}).toReal

def UniformProbabilityConjecture : Prop :=
  ∀ b d : ℕ, 1 ≤ b → 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ C : ℝ, ∀ L : Data b d, Admissible L → 1 - δ ≤ boundedProbability L C

def witnessData (e : ℝ) : Data 2 3 := ![![2, 2], ![e, 2 * e], ![0, 1]]
def epsilon (m : ℕ) : ℝ := 1 / ((m : ℝ) + 6)

def X (w : Sample 2 3) : Mat 2 :=
  (omega w 1)⁻¹ * Matrix.diagonal (![1, 2] : Fin 2 → ℝ) * omega w 1
def P (w : Sample 2 3) : Mat 2 :=
  (omega w 2)⁻¹ * Matrix.diagonal (![0, 1] : Fin 2 → ℝ) * omega w 2
def kappa (w : Sample 2 3) : ℝ := ((1 - P w) * X w).trace
def Q (w : Sample 2 3) : Mat 2 := (1 - P w) * X w * P w
def limitMatrix (w : Sample 2 3) : Mat 2 := (-1 / kappa w) • Q w

def rationalSample : Sample 2 3 :=
  fun ij => (![ (1 : Mat 2), 1, !![1, 2; 3, 5]] : Fin 3 → Mat 2) ij.1 ij.2.1 ij.2.2

end NLA.KE05
end
