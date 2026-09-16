/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted formalization of Matthew J. Colbrook's complete IV-03 criterion.
The proof modules never import the statements-only Challenge. -/
import NLA.IV03.IntervalInduction
import LeanCert.Tactic.IntervalAuto.PointIneq
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IV03

theorem vertex_formula {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) :
    vertex L U s i j = center L U + s •
      (Matrix.diagonal (signVector i) * radius L U * Matrix.diagonal (signVector j)) :=
  vertex_formula_proved L U s i j

theorem vertices_admissible {n : ℕ} (L U : Mat n) (h : OrderedEndpoints L U)
    (i j : Fin n) (s : ℝ) (hs : s ∈ ({(-1 : ℝ), 1} : Set ℝ)) :
    vertex L U s i j ∈ intervalFamily L U :=
  vertices_admissible_proved L U h i j s hs

theorem nSquaredCriterion {n : ℕ} (hn : 1 ≤ n) (L U : Mat n)
    (h : OrderedEndpoints L U) :
    (∀ A ∈ intervalFamily L U, IsInverseM A) ↔
      ∀ i j : Fin n, IsInverseM (vertex L U (-1) i j) := by
  constructor
  · intro hAll i j
    exact hAll _ (vertices_admissible L U h i j (-1) (by simp))
  · exact interval_inverseM_from_vertices n hn L U h

theorem twoSignCriterion : TwoSignCriterion := by
  intro n hn L U h
  constructor
  · intro hAll i j s hs
    exact hAll _ (vertices_admissible L U h i j s hs)
  · intro hTests
    apply (nSquaredCriterion hn L U h).mpr
    intro i j
    exact hTests i j (-1) (by simp)

end NLA.IV03
#assert_trust kernel NLA.IV03.vertex_formula
#assert_trust kernel NLA.IV03.vertices_admissible
#assert_trust kernel NLA.IV03.nSquaredCriterion
#assert_trust kernel NLA.IV03.twoSignCriterion
#print axioms NLA.IV03.vertex_formula
#print axioms NLA.IV03.vertices_admissible
#print axioms NLA.IV03.nSquaredCriterion
#print axioms NLA.IV03.twoSignCriterion
