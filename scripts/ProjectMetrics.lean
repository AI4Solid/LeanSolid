import Lean
import LeanSolid

open Lean Elab Command

private def libraryModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some i => (`LeanSolid).isPrefixOf env.allImportedModuleNames[i.toNat]!
  | none => false

run_cmd do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun found name info =>
    if libraryModule env name then found.push (name, info) else found
  let mut authored : Nat := 0
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in declarations do
    let isAuthored ← findDeclarationRangesCore? name
    if isAuthored.isNone then continue
    match info with
    | .thmInfo _ =>
      theorems := theorems + 1
      let axioms ← collectAxioms name
      if axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) then
        checked := checked + 1
    | .defnInfo _ | .opaqueInfo _ | .inductInfo _ | .axiomInfo _ => pure ()
    | _ => continue
    authored := authored + 1
  logInfo m!"LEANSOLID_METRICS {authored} {checked} {theorems}"
