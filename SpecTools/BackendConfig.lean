import SpecTools.Model

namespace SpecTools.Model
open Lean

/-- Parse deployment configuration without choosing a provider or a model for the caller. -/
def backendOfJson (json : Json) : Except String Backend := do
  let model ← json.getObjValAs? String "model"
  let destination ← json.getObjValAs? String "dataGoesTo"
  if model.trimAscii.isEmpty then throw "backend model must be nonempty"
  if destination.trimAscii.isEmpty then throw "backend dataGoesTo must describe its destination"
  let adapter ← json.getObjValAs? String "adapter"
  let harness ← match adapter with
    | "codex" => pure Harness.codex
    | "claude-code" => pure Harness.claudeCode
    | "command" => do
      let executable ← json.getObjValAs? String "command"
      if executable.trimAscii.isEmpty then throw "backend command must be nonempty"
      let arguments ← json.getObjValAs? (List String) "args"
      pure (Harness.command executable arguments)
    | _ => throw s!"unknown adapter {adapter}; use codex, claude-code or command"
  return { harness, model, dataGoesTo := destination }

/-- Read the explicitly selected configuration; absence never silently chooses a remote backend. -/
def configuredBackend : IO Backend := do
  let some path ← IO.getEnv "SPEC_TOOLS_BACKEND"
    | throw (IO.userError "set SPEC_TOOLS_BACKEND to a backend JSON configuration file")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (backendOfJson json)

/-- The CLI's model argument remains authoritative when selecting a configured adapter. -/
def selectedBackend (adapter model : String) : IO Backend := do
  if model.trimAscii.isEmpty then throw (IO.userError "backend model must be nonempty")
  if adapter == "configured" then return { (← configuredBackend) with model }
  IO.ofExcept (backendOfJson (Json.mkObj [("adapter", toJson adapter),
    ("model", toJson model), ("dataGoesTo", toJson s!"{adapter}'s configured destination")]))

end SpecTools.Model
