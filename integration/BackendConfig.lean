-- SPDX-License-Identifier: Apache-2.0
import SpecTools.BackendConfig

open Lean SpecTools.Model

private def selectWith (path : String) (config : Json) (model := "default") : IO Backend := do
  IO.FS.writeFile path config.compress
  selectedBackend "configured" model

private def checkRefusal (path : String) (config : Json) (model diagnostic : String) : IO Unit := do
  match ← (selectWith path config model).toBaseIO with
  | .ok backend => throw (IO.userError s!"Unexpected backend: {repr backend}")
  | .error error =>
    unless ((toString error).splitOn diagnostic).length > 1 do
      throw (IO.userError s!"Expected {diagnostic}, got {error}")

#eval show IO Unit from do
  let some path ← IO.getEnv "SPEC_TOOLS_BACKEND" |
    throw (IO.userError "Expected an isolated backend configuration path")
  if ← (System.FilePath.mk path).pathExists then
    throw (IO.userError "The fixture requires a new backend configuration file")
  for (adapter, harness) in [("codex", Harness.codex), ("claude-code", .claudeCode),
      ("command", .command "cat" ["-n"])] do
    let config := Json.mkObj [("adapter", toJson adapter), ("model", toJson "chosen"),
      ("dataGoesTo", toJson "chosen destination"), ("command", toJson "cat"),
      ("args", toJson ["-n"])]
    let expected : Backend := ⟨harness, "chosen", "chosen destination", none⟩
    let loaded ← selectWith path config
    unless loaded = expected do
      throw (IO.userError s!"{adapter}: configuration changed: {repr loaded}")
    let explicit := config.setObjVal! "effort" (toJson "medium")
    let overridden ← selectWith path explicit "override"
    unless overridden = { expected with model := "override", effort := some "medium" } do
      throw (IO.userError s!"{adapter}: override changed other fields: {repr overridden}")
    checkRefusal path (config.setObjVal! "effort" (toJson " ")) "default"
      "backend effort must be nonempty when given"
    checkRefusal path (Json.mkObj [("adapter", toJson adapter)]) "default" "String expected"
    for model in ["", "  "] do
      checkRefusal path config model "backend model must be nonempty"
