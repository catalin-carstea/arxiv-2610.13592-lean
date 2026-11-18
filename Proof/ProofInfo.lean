module
public import Lean
public section
open Lean Elab Command

/-- Elaborate an ordinary command without retaining its internal editor info tree.
The surrounding command info node, diagnostics, elaboration and kernel checking remain.
This changes only InfoState.enabled and restores it even on failure. -/
syntax (name := withoutProofInfo) "without_proof_info" " in " command : command

@[command_elab withoutProofInfo]
meta def elabWithoutProofInfo : CommandElab := fun stx => do
  let enabled := (← getInfoState).enabled
  modifyInfoState fun s => { s with enabled := false }
  try
    elabCommand stx[2]
  finally
    modifyInfoState fun s => { s with enabled := enabled }
