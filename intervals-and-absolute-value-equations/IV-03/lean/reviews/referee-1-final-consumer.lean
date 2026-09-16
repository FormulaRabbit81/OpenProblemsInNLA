/- Trusted statements only. These placeholders establish no result and must
never be imported by a future Solution. -/
import Solution
set_option autoImplicit false
noncomputable section
namespace NLA.IV03

example {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) :
    vertex L U s i j = center L U + s •
      (Matrix.diagonal (signVector i) * radius L U * Matrix.diagonal (signVector j)) := by
  exact vertex_formula L U s i j

example {n : ℕ} (L U : Mat n) (h : OrderedEndpoints L U)
    (i j : Fin n) (s : ℝ) (hs : s ∈ ({(-1 : ℝ), 1} : Set ℝ)) :
    vertex L U s i j ∈ intervalFamily L U := by
  exact vertices_admissible L U h i j s hs

example {n : ℕ} (hn : 1 ≤ n) (L U : Mat n)
    (h : OrderedEndpoints L U) :
    (∀ A ∈ intervalFamily L U, IsInverseM A) ↔
      ∀ i j : Fin n, IsInverseM (vertex L U (-1) i j) := by
  exact nSquaredCriterion hn L U h

example : TwoSignCriterion := by
  exact twoSignCriterion

end NLA.IV03

#assert_trust kernel NLA.IV03.vertex_formula
#print axioms NLA.IV03.vertex_formula
#assert_trust kernel NLA.IV03.vertices_admissible
#print axioms NLA.IV03.vertices_admissible
#assert_trust kernel NLA.IV03.nSquaredCriterion
#print axioms NLA.IV03.nSquaredCriterion
#assert_trust kernel NLA.IV03.twoSignCriterion
#print axioms NLA.IV03.twoSignCriterion
