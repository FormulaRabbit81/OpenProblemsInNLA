import IE22.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (`NLA).isPrefixOf name then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun axiomName ↦ !allowed.contains axiomName
      unless unexpected.isEmpty do
        throwError "{name} uses unapproved axioms: {unexpected}"
      checked := checked + 1
  logInfo m!"Checked {checked} NLA declarations: only propext, Classical.choice and Quot.sound."
