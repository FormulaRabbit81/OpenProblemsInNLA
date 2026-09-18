/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Shared transports between equality decisions for the literal transition coefficients.
-/
import NLA.NM04.TransitionSupport
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04

-- Only equality decisions change; the finite enumerations remain fixed.
attribute [local instance] Classical.propDecidable

/-- Transport support propositions along equality of decision instances. -/
theorem support_decision_transport {α β : Type*}
    (P : DecidableEq α → DecidableEq β → Prop)
    {da da' : DecidableEq α} {db db' : DecidableEq β} (h : P da db) : P da' db' :=
  (congrArg₂ P (Subsingleton.elim da da') (Subsingleton.elim db db')).mp h

/-- The column coefficient is independent of the equality decision on row labels. -/
theorem column_coefficient_all_decisions {α β : Type*}
    [Fintype β] [LinearOrder β] (I J : MinorIndex α β) (x : ℤ)
    (h : columnExchangeCoefficient I J = x) :
    ∀ d : DecidableEq α, @columnExchangeCoefficient α β _ d _ I J = x := by
  intro d
  exact (congrArg (fun e : DecidableEq α =>
    @columnExchangeCoefficient α β _ e _ I J = x) (Subsingleton.elim _ d)).mp h

/-- The row coefficient is independent of the equality decision on column labels. -/
theorem row_coefficient_all_decisions {α β : Type*}
    [Fintype α] [LinearOrder α] (I J : MinorIndex α β) (x : ℤ)
    (h : rowExchangeCoefficient I J = x) :
    ∀ d : DecidableEq β, @rowExchangeCoefficient α β _ _ d I J = x := by
  intro d
  exact (congrArg (fun e : DecidableEq β =>
    @rowExchangeCoefficient α β _ _ e I J = x) (Subsingleton.elim _ d)).mp h

#print axioms support_decision_transport
#assert_trust kernel support_decision_transport
#print axioms column_coefficient_all_decisions
#assert_trust kernel column_coefficient_all_decisions
#print axioms row_coefficient_all_decisions
#assert_trust kernel row_coefficient_all_decisions

end NLA.NM04
