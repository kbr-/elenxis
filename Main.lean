import SpecTools

/-- The commands, each with what it does. -/
def commands : List (String × String) := [
  ("ask", "ask one question of a backend: ask HARNESS MODEL SCHEMA-FILE PROMPT-FILE [TIMEOUT-MS]")
]

def usage : String :=
  "usage: spec-tools COMMAND ...\n" ++ "\n".intercalate (commands.map fun (c, d) => s!"  {c}: {d}")

open SpecTools.Model in
def ask (args : List String) : IO UInt32 := do
  match args with
  | [harness, model, schemaFile, promptFile] | [harness, model, schemaFile, promptFile, _] =>
    let timeoutMs := (args.drop 4).head? |>.bind String.toNat? |>.getD 120000
    let harness ← match harness with
      | "claude-code" => pure Harness.claudeCode
      | "codex" => pure Harness.codex
      | other => do IO.eprintln s!"unknown harness `{other}`: claude-code or codex"; return 2
    let schema ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile schemaFile))
    let backend : Backend := { harness, model, dataGoesTo := s!"{harness.name}'s provider" }
    let scratch ← IO.FS.createTempDir
    let result ← SpecTools.Model.ask liveRunner [backend] backend
      { prompt := ← IO.FS.readFile promptFile, schema, timeoutMs } scratch
    IO.FS.removeDirAll scratch
    match result with
    | .ok outcome =>
      IO.println outcome.answer.compress
      IO.eprintln s!"cost: {outcome.cost.millis} ms, tokens: {outcome.cost.tokens}"
      return 0
    | .error failure => IO.eprintln failure.describe; return 1
  | _ => IO.eprintln usage; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "ask" :: rest => ask rest
  | [] => IO.eprintln usage; return 2
  | command :: _ => IO.eprintln s!"unknown command `{command}`\n{usage}"; return 2
