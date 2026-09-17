/- Trusted statements only. These placeholders establish no result and must
never be imported by a future Solution. -/
import NLA.IV03.Definitions
set_option autoImplicit false
noncomputable section
namespace NLA.IV03

theorem vertex_formula {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) :
    vertex L U s i j = center L U + s •
      (Matrix.diagonal (signVector i) * radius L U * Matrix.diagonal (signVector j)) := by sorry

theorem vertices_admissible {n : ℕ} (L U : Mat n) (h : OrderedEndpoints L U)
    (i j : Fin n) (s : ℝ) (hs : s ∈ ({(-1 : ℝ), 1} : Set ℝ)) :
    vertex L U s i j ∈ intervalFamily L U := by sorry

theorem nSquaredCriterion {n : ℕ} (hn : 1 ≤ n) (L U : Mat n)
    (h : OrderedEndpoints L U) :
    (∀ A ∈ intervalFamily L U, IsInverseM A) ↔
      ∀ i j : Fin n, IsInverseM (vertex L U (-1) i j) := by sorry

theorem twoSignCriterion : TwoSignCriterion := by sorry

end NLA.IV03
