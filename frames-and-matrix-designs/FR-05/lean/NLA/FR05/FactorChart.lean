/-
An alternative local rank-two chart for the planted-law argument in §3.4.

The source uses a Schur-complement chart.  Near its seed, the polynomial
factor chart below has the same real coordinates and the same first-order derivatives,
but writes every matrix directly as `xxᴴ - yyᴴ`.  This removes a separate
spectral/inertia conversion at the end of the proof: a zero of the
measurement equations immediately gives two inequivalent signals with equal
measurements.
-/
import NLA.FR05.Obstruction
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- Assemble two distinguished coordinates and an `n`-coordinate tail into a
signal of ambient dimension `n + 2`. -/
def joinTwo {n : ℕ} (u v : ℂ) (w : Signal n) : Signal (n + 2) :=
  fun i =>
    if h0 : i.1 = 0 then u
    else if h1 : i.1 = 1 then v
    else w ⟨i.1 - 2, by omega⟩

theorem joinTwo_zero {n : ℕ} (u v : ℂ) (w : Signal n) :
    joinTwo u v w ⟨0, Nat.zero_lt_succ _⟩ = u := by
  simp [joinTwo]

theorem joinTwo_one {n : ℕ} (u v : ℂ) (w : Signal n) :
    joinTwo u v w ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ = v := by
  simp [joinTwo]

/-- Positive factor in the local polynomial chart.  The `s/4` choice makes
the differential at the seed agree coordinate-for-coordinate with (3.19),
while avoiding a transcendental coordinate change. -/
def factorPlus {n : ℕ} (s : ℝ) (b : ℂ) (z : Signal n) : Signal (n + 2) :=
  joinTwo (1 + s / 4) (star b) z

/-- Negative factor in the local polynomial chart. -/
def factorMinus {n : ℕ} (s : ℝ) (t : Signal n) : Signal (n + 2) :=
  joinTwo 0 (1 - s / 4) (-t)

/-- A factorized rank-at-most-two Hermitian chart through
`diag(1,-1,0,...)`. -/
def factorChart {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  rankOneDifference (factorPlus s b z) (factorMinus s t)

/-- The two factors in the chart are never related by a global phase: their
first coordinates are respectively nonzero and zero. -/
theorem factorPlus_not_globallyPhased_factorMinus {n : ℕ}
    (s : ℝ) (b : ℂ) (z t : Signal n) (hs : |s| ≤ 1) :
    ¬ GloballyPhased (factorPlus s b z) (factorMinus s t) := by
  intro hphase
  obtain ⟨θ, hθ⟩ := hphase
  have hzero := congrFun hθ ⟨0, Nat.zero_lt_succ _⟩
  have hs' : -1 ≤ s ∧ s ≤ 1 := abs_le.mp hs
  have hpositive : 0 < 1 + s / 4 := by
    linarith
  have hnonzero :
      Complex.exp (θ * Complex.I) * (1 + s / 4 : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.exp_ne_zero _
    · exact_mod_cast hpositive.ne'
  apply hnonzero
  simpa [factorPlus, factorMinus, joinTwo] using hzero.symm

/-- The exact deterministic endpoint of the planted argument for the factor
chart.  A simultaneous zero of the real quadratic equations refutes the
original all-signal phase-retrieval predicate. -/
theorem factorChart_not_phaseRetrievalInjective_of_quadraticForm_zero
    {m n : ℕ} (A : Frame m (n + 2))
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (hs : |s| ≤ 1)
    (hzero : ∀ i, quadraticForm (factorChart s b z t) (conjugateRow A i) = 0) :
    ¬ PhaseRetrievalInjective A := by
  apply not_phaseRetrievalInjective_of_rankOneDifference_quadraticForm_eq_zero
    A (factorPlus s b z) (factorMinus s t)
  · simpa [factorChart] using hzero
  · exact factorPlus_not_globallyPhased_factorMinus s b z t hs

theorem factorPlus_zero {n : ℕ} :
    factorPlus (n := n) 0 0 0 =
      standardBasis (firstCoordinate (n + 2) (by omega)) := by
  funext i
  by_cases hi : i = firstCoordinate (n + 2) (by omega)
  · subst i
    simp [factorPlus, joinTwo, standardBasis, firstCoordinate]
  · have hi0 : i.1 ≠ 0 := by
      intro hzero
      apply hi
      apply Fin.ext
      simpa [firstCoordinate] using hzero
    have hi' : i ≠ (0 : Fin (n + 2)) := by
      intro heq
      apply hi
      simpa [firstCoordinate] using heq
    simp [factorPlus, joinTwo, standardBasis, firstCoordinate, hi0, hi']

theorem factorMinus_zero {n : ℕ} :
    factorMinus (n := n) 0 0 =
      standardBasis (secondCoordinate (n + 2) (by omega)) := by
  funext i
  by_cases hi : i = secondCoordinate (n + 2) (by omega)
  · subst i
    simp [factorMinus, joinTwo, standardBasis, secondCoordinate]
  · have hi1 : i.1 ≠ 1 := by
      intro hone
      apply hi
      apply Fin.ext
      simpa [secondCoordinate] using hone
    have hi' : i ≠ (1 : Fin (n + 2)) := by
      intro heq
      apply hi
      simpa [secondCoordinate] using heq
    simp [factorMinus, joinTwo, standardBasis, secondCoordinate, hi1, hi']

end NLA.FR05
