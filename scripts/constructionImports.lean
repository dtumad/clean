import Clean.Examples.ConstructionEnsemble

open Lean in
run_cmd do
  let modules := (← getEnv).header.moduleNames
  for name in modules do
    let root := name.getRoot.toString
    if ["SP1Clean", "ToClean", "Sail", "LeanRV64D", "PolyFun", "ToPolyFun"].contains root then
      throwError "unexpected construction dependency: {name}"
    logInfo m!"{name}"
  logInfo m!"imported modules: {modules.size}"
