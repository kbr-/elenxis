-- SPDX-License-Identifier: Apache-2.0
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

/-- The selected backend as an explicit configuration for a variant's tool calls. -/
def backendConfigJson (backend : Backend) : Json :=
  Json.mkObj ([
    ("adapter", toJson (match backend.harness with
      | .command .. => "command"
      | harness => harness.name)),
    ("model", toJson backend.model), ("dataGoesTo", toJson backend.dataGoesTo)] ++
    (backend.effort.toList.map fun effort => ("effort", toJson effort)) ++
    (match backend.harness with
      | .command command args => [("command", toJson command), ("args", toJson args)]
      | _ => []))

theorem codexConfigRoundTrip :
    let b : Backend := ⟨.codex, "gpt-6.2-sol", "existing Codex account", some "medium"⟩
    (backendOfJson (backendConfigJson b)).toOption = some b := by native_decide

def callerBackend (inCodex : Bool) : Except String Backend :=
  if inCodex then
    .ok ⟨.codex, "gpt-6.2-sol", "OpenAI, through the calling Codex login", some "medium"⟩
  else .error "set SPEC_TOOLS_BACKEND to a backend JSON configuration file"

theorem codexCallerUsesSolMedium :
    (callerBackend true).toOption.map (fun b => (b.harness, b.model, b.effort)) =
      some (.codex, "gpt-6.2-sol", some "medium") ∧
    (callerBackend false).toOption.isNone = true := by native_decide

/-- Configuration forwarded when a variant check starts a protected Lean subprocess. -/
def backendEnvironment : List String :=
  ["SPEC_TOOLS_HOST", "SPEC_TOOLS_BACKEND", "CODEX_THREAD_ID", "CODEX_HOME"]

/-- An explicit file takes precedence over a default derived from the calling harness. -/
def configuredBackend : IO Backend := do
  if let some path ← IO.getEnv "SPEC_TOOLS_BACKEND" then
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
    return ← IO.ofExcept (backendOfJson json)
  let inCodex := (← IO.getEnv "CODEX_THREAD_ID").any (!·.trimAscii.isEmpty)
  IO.ofExcept (callerBackend inCodex)

/-- The CLI's model argument remains authoritative when selecting a configured adapter. -/
def selectedBackend (adapter model : String) : IO Backend := do
  IO.ofExcept (validateModel model)
  if adapter == "configured" then
    let backend ← configuredBackend
    return if model == "default" then backend else { backend with model }
  IO.ofExcept (backendOfJson (Json.mkObj [("adapter", toJson adapter),
    ("model", toJson model), ("dataGoesTo", toJson s!"{adapter}'s configured destination")]))

end SpecTools.Model
