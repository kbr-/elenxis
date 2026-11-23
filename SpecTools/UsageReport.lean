import SpecTools.Model
import Std.Sync.Mutex

/-!
Recording a call's usage and trace, outside any specification:

- `SPEC_TOOLS_USAGE` names a file each call appends its usage record to, one JSON line (`tool`,
  `usage`); `spec-tools check` sets it in a variant's copy, so a run reads back what its tools used.
- `SPEC_TOOLS_TRACE` names a directory each call appends one JSON line to, in `calls-PID.jsonl`: the
  time, the tool, the backend, the prompt, the schema, the raw answer (refused proposals included)
  or the failure, and the usage. A directory that can't be written fails before the call, so no
  call goes untraced when a trace was asked for. Unset, nothing is written: prompts carry a
  target's text.
-/

namespace SpecTools.Usage
open Lean SpecTools.Model

/-- The backend as the usage line names it: adapter, model and effort. -/
def brief (b : Backend) : String :=
  let effort := match b.effort with
    | some e => s!", effort {e}"
    | none => ""
  s!"{b.harness.name} {b.model}{effort}"

/-- The trace file of this process, opened before any call; `none` when no trace was asked for. -/
def traceFile : IO (Option IO.FS.Handle) := do
  let some dir ← IO.getEnv "SPEC_TOOLS_TRACE" | return none
  IO.FS.createDirAll dir
  let path := System.FilePath.mk dir / s!"calls-{← IO.Process.getPID}.jsonl"
  return some (← IO.FS.Handle.mk path .append)

private initialize journalLock : Std.Mutex Unit ← Std.Mutex.new ()

private def appendRecord (handle : IO.FS.Handle) (record : Json) : IO Unit := do
  let line := record.compress
  journalLock.atomically do
    handle.putStrLn line
    handle.flush

/-- Append `u` to the file `SPEC_TOOLS_USAGE` names, if set. -/
def recordUsage (tool : String) (u : Usage) : IO Unit := do
  let some path ← IO.getEnv "SPEC_TOOLS_USAGE" | return
  let h ← IO.FS.Handle.mk path .append
  appendRecord h (Json.mkObj [("tool", Json.str tool), ("usage", asJson u)])

/-- The records a usage file holds, totalled; an absent file holds none. -/
def readRecorded (path : System.FilePath) : IO Usage := do
  unless ← path.pathExists do return {}
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  return total (lines.filterMap fun l => do
    let j ← (Json.parse l).toOption
    fromJson? (← (j.getObjVal? "usage").toOption))

/-- Ask as `askWithUsage` does, recording the call's usage and, when asked for, its trace. -/
def askRecorded (tool : String) (runner : Runner) (allowed : List Backend) (backend : Backend)
    (question : Question) (scratch : System.FilePath) : IO (Except Failure Outcome × Usage) := do
  let trace ← traceFile
  let (result, u) ← askWithUsage runner allowed backend question scratch
  recordUsage tool u
  if let some h := trace then
    let answer := match result with
      | .ok o => Json.mkObj [("answer", o.answer)]
      | .error f => Json.mkObj [("failure", Json.str f.describe)]
    appendRecord h (Json.mkObj [("time", Json.str (toString (← IO.monoMsNow))), ("tool", Json.str tool),
      ("backend", Json.str (brief backend)), ("prompt", Json.str question.prompt),
      ("schema", question.schema), ("result", answer), ("usage", asJson u)])
  return (result, u)

end SpecTools.Usage
