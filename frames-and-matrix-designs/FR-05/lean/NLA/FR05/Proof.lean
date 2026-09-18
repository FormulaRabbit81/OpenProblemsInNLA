/-
Current checked checkpoint. The source's quantitative planted-law, Haar-overlap
and likelihood-comparison estimates are deliberately absent rather than
represented by axioms or unproved declarations.
-/
import NLA.FR05.Obstruction
import NLA.FR05.RankTwoSeed
import NLA.FR05.RankTwoChart
import NLA.FR05.SourceParameters
import NLA.FR05.FactorChart
import NLA.FR05.FactorTaylor
import NLA.FR05.Planted
import NLA.FR05.PlantedTaylor
import NLA.FR05.Jacobian
import NLA.FR05.DerivativeControl
import NLA.FR05.DerivativeNorm
import NLA.FR05.DerivativeGoodEvent
import NLA.FR05.SourceDerivativeBounds
import NLA.FR05.SourceGoodEvent
import NLA.FR05.Newton
import NLA.FR05.PlantedBounds
import NLA.FR05.GaussianTail
import NLA.FR05.SmallBallAlgebra
import NLA.FR05.GaussianSmallBall
import NLA.FR05.PhaseSmallBall
import NLA.FR05.PhaseAffine
import NLA.FR05.PhaseShift
import NLA.FR05.PhaseAbsolute
import NLA.FR05.TailVariancePhase
import NLA.FR05.GaussianProjection
import NLA.FR05.GaussianProjectionSmallBall
import NLA.FR05.TailConditionalSmallBall
import NLA.FR05.SourceTailConditional
import NLA.FR05.SourceTailBridge
import NLA.FR05.SourceTailGlobal
import NLA.FR05.SourceRowSmallBall
import NLA.FR05.ProductSections
import NLA.FR05.SourceConditional
import NLA.FR05.PlantedLaw
import NLA.FR05.SourceRowBridge
import NLA.FR05.IidRowSplit
import NLA.FR05.RadialTail
import NLA.FR05.SourceMarginals
import NLA.FR05.FiniteRowEnergy
import NLA.FR05.LeastSingular
import NLA.FR05.RowNormal
import NLA.FR05.SourceJacobianMatrix
import NLA.FR05.SourceJacobianEnergy
import NLA.FR05.ImbalancePerturbation
import NLA.FR05.SourceMatrixPerturbation
import NLA.FR05.MainReduction
import NLA.FR05.LikelihoodAlgebra

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- Existential form of the all-dimension exact ambiguity checkpoint. -/
theorem explicit_noninjective_frame_proved (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  refine ⟨flatFrame (4 * d - 5) d, ?_⟩
  exact flatFrame_not_phaseRetrievalInjective d hd

end NLA.FR05
