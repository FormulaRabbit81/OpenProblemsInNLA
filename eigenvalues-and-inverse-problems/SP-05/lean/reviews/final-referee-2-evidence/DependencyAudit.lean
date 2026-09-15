import Solution
import Lean.Util.FoldConsts

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for root in [``NLA.SP05.skew_witness, ``NLA.SP05.sector_minima, ``NLA.SP05.canonical_result] do
    let mut pending := [root]
    let mut seen : List Name := []
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if !seen.contains name then
        seen := name :: seen
        let some ci := env.find? name | throwError "Missing constant {name}"
        let dependencies := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
        for child in dependencies do
          if child.toString.startsWith "NLA.SP05." then
            pending := child :: pending
    unless seen.contains ``NLA.SP05.skew_norm_positive_certificate do
      throwError "Kernel certificate missing from actual project dependency closure of {root}"
    logInfo m!"{root}: consumed certificate present in actual expression dependency closure ({seen.length} project constants)"
