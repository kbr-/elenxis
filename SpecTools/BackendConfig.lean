import SpecTools.Model

namespace SpecTools.Model
open Lean

def validateModel (model : String) : Except String Unit :=
  if model.trimAscii.isEmpty then .error "backend model must be nonempty" else .ok ()

theorem validateModel_iff (model : String) :
    validateModel model = .ok () ↔ model.trimAscii.isEmpty = false := by
  simp [validateModel]

/-- Parse deployment configuration without choosing a provider or a model for the caller. -/
def backendOfJson (json : Json) : Except String Backend := do
  let model ← json.getObjValAs? String "model"
  let destination ← json.getObjValAs? String "dataGoesTo"
  validateModel model
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
  -- The reasoning effort, when given, is passed to the harness as it is written; an empty one is
  -- refused, and its absence leaves the harness's own default.
  let effort ← match json.getObjVal? "effort" with
    | .error _ => pure none
    | .ok _ => do
      let e ← json.getObjValAs? String "effort"
      if e.trimAscii.isEmpty then throw "backend effort must be nonempty when given"
      pure (some e)
  return { harness, model, dataGoesTo := destination, effort }

theorem backendOfJson_model {json : Json} {backend : Backend}
    (result : backendOfJson json = .ok backend) :
    json.getObjValAs? String "model" = .ok backend.model := by
  simp only [backendOfJson, bind, Except.bind, pure, Except.pure] at result
  repeat' first | split at result | cases result
  all_goals simp_all

/-- Read the explicitly selected configuration; absence never silently chooses a remote backend. -/
def configuredBackend : IO Backend := do
  let some path ← IO.getEnv "SPEC_TOOLS_BACKEND"
    | throw (IO.userError "set SPEC_TOOLS_BACKEND to a backend JSON configuration file")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (backendOfJson json)

/-- The CLI's model argument remains authoritative when selecting a configured adapter. -/
def selectedBackend (adapter model : String) : IO Backend := do
  IO.ofExcept (validateModel model)
  if adapter == "configured" then return { (← configuredBackend) with model }
  IO.ofExcept (backendOfJson (Json.mkObj [("adapter", toJson adapter),
    ("model", toJson model), ("dataGoesTo", toJson s!"{adapter}'s configured destination")]))

end SpecTools.Model
