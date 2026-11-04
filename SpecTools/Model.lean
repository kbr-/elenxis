import Lean.Data.Json
import SpecTools.Schema

/-!
The model interface: the machinery asks a question of a backend and gets back a parsed answer with
its cost, or an error naming the backend. Only the adapters (`invocation`, `readAnswer`) know how a
harness is called; the effects (running a process, timing it) sit in the `Runner` passed in, so tests
script it and no test reaches a model.

A question can't act: Claude Code runs with every tool disabled (`--tools ""`) and without the
user's settings, hooks or instructions (`--safe-mode`); Codex runs with `--sandbox read-only`; each
runs in an empty scratch directory. An agent run, the other kind of call, acts only in the copy it is
given (`agentInvocation`).
-/

namespace SpecTools.Model
open Lean

inductive Harness where
  | claudeCode
  | codex
  deriving Repr, BEq, Inhabited

def Harness.name : Harness → String
  | .claudeCode => "claude-code"
  | .codex => "codex"

/-- A harness, the model it runs, and where the prompt's data goes when it runs. -/
structure Backend where
  harness : Harness
  model : String
  dataGoesTo : String
  deriving Repr, BEq, Inhabited

def Backend.name (b : Backend) : String := s!"{b.harness.name}/{b.model}"

/-- A prompt and the JSON Schema its answer must meet, bounded by a timeout. -/
structure Question where
  prompt : String
  schema : Json
  timeoutMs : Nat

/-- What a call cost: its wall-clock time, and tokens where the harness reports them. -/
structure Cost where
  millis : Nat
  tokens : Option Nat := none
  deriving Repr, BEq

structure Outcome where
  answer : Json
  cost : Cost

/-- Why a call gave no answer, naming the backend. -/
inductive Failure where
  | refused (backend : String) (reason : String)
  | timedOut (backend : String) (afterMs : Nat)
  | exited (backend : String) (code : UInt32) (firstLines : String)
  | malformed (backend : String) (reason : String)
  deriving Repr, BEq

def Failure.describe : Failure → String
  | .refused b r => s!"{b}: refused before running: {r}"
  | .timedOut b ms => s!"{b}: no answer within {ms} ms"
  | .exited b c lines => s!"{b}: exited with status {c}: {lines}"
  | .malformed b r => s!"{b}: answer unusable: {r}"

/-- One process to run: its command, arguments (the prompt last), working directory, and the files
to write into the working directory first. -/
structure Invocation where
  cmd : String
  args : Array String
  cwd : System.FilePath
  files : List (String × String) := []
  deriving Repr, BEq, Inhabited

/-- The largest prompt passed as an argument: half the system's 2 MiB argument limit (`getconf
ARG_MAX` on this machine), leaving room for the other arguments and the environment. -/
def maxPromptBytes : Nat := 1048576

/-- What a finished process left: its status, its output, the files it wrote that the adapter reads
back, and its time. -/
structure Ran where
  exitCode : UInt32
  stdout : String
  stderr : String
  readBack : List (String × String) := []
  millis : Nat

/-- Runs an invocation within a time limit, reading back the named files; `none` when it overran. -/
abbrev Runner := Invocation → (readBack : List String) → (timeoutMs : Nat) → IO (Option Ran)

private def firstLines (text : String) (n : Nat := 5) : String :=
  " | ".intercalate ((text.splitOn "\n").filter (!·.trimAscii.isEmpty) |>.take n)

/-- The command line asking `question` of `backend`, run in the empty directory `scratch`. -/
def invocation (backend : Backend) (question : Question) (scratch : System.FilePath) : Invocation :=
  match backend.harness with
  | .claudeCode =>
    { cmd := "claude"
      args := #["-p", "--safe-mode", "--tools", "", "--no-session-persistence",
        "--model", backend.model, "--output-format", "json",
        "--json-schema", question.schema.compress, "--", question.prompt]
      cwd := scratch }
  | .codex =>
    { cmd := "codex"
      args := #["exec", "--skip-git-repo-check", "--ephemeral", "--sandbox", "read-only",
        "-m", backend.model, "--output-schema", "schema.json", "-o", "answer.json", "--",
        question.prompt]
      cwd := scratch
      files := [("schema.json", question.schema.compress)] }

/-- The files the adapter reads back after the run. -/
def readBackFiles : Harness → List String
  | .claudeCode => []
  | .codex => ["answer.json"]

private def tokensOf (report : Json) : Option Nat :=
  match report.getObjVal? "usage" with
  | .ok usage =>
    let field (k : String) : Nat := (usage.getObjValAs? Nat k).toOption.getD 0
    some (field "input_tokens" + field "cache_creation_input_tokens" + field "cache_read_input_tokens"
      + field "output_tokens")
  | .error _ => none

/-- The answer a finished run carries, before the schema check. -/
def readAnswer (backend : Backend) (ran : Ran) : Except Failure (Json × Option Nat) := do
  let name := backend.name
  if ran.exitCode != 0 then
    throw (.exited name ran.exitCode (firstLines (ran.stderr ++ "\n" ++ ran.stdout)))
  match backend.harness with
  | .claudeCode =>
    let report ← (Json.parse ran.stdout).mapError fun e => .malformed name s!"output is no JSON: {e}"
    if (report.getObjValAs? Bool "is_error").toOption == some true then
      throw (.malformed name s!"the harness reported an error: {firstLines ran.stdout}")
    match report.getObjVal? "structured_output" with
    | .ok answer => return (answer, tokensOf report)
    | .error _ => throw (.malformed name "no structured_output in the harness's report")
  | .codex =>
    match ran.readBack.lookup "answer.json" with
    | none => throw (.malformed name "the answer file was not written")
    | some text =>
      let answer ← (Json.parse text).mapError fun e => .malformed name s!"answer is no JSON: {e}"
      return (answer, none)

/-- Ask `question` of `backend` through `runner`, in the empty directory `scratch`, when the project
allows the backend. The answer is returned only when it meets the question's schema. -/
def ask (runner : Runner) (allowed : List Backend) (backend : Backend) (question : Question)
    (scratch : System.FilePath) : IO (Except Failure Outcome) := do
  let name := backend.name
  unless allowed.contains backend do
    return .error (.refused name "the project doesn't allow this backend")
  if let some problem := Schema.unsupported question.schema then
    return .error (.refused name s!"the question's schema: {problem}")
  if question.prompt.utf8ByteSize > maxPromptBytes then
    return .error (.refused name
      s!"the prompt is {question.prompt.utf8ByteSize} bytes, over {maxPromptBytes}")
  match ← runner (invocation backend question scratch) (readBackFiles backend.harness)
      question.timeoutMs with
  | none => return .error (.timedOut name question.timeoutMs)
  | some ran =>
    return do
      let (answer, tokens) ← readAnswer backend ran
      if let some why := Schema.violation question.schema answer then
        throw (.malformed name s!"answer breaks the schema at {why}")
      return { answer, cost := { millis := ran.millis, tokens } }

/-- An agent run: `prompt` given to `backend` working in `workdir` (a copy made for the run), able to
use only `tools`. Claude Code gets exactly those tools, each allowed; Codex gets a sandbox that
writes only in `workdir`, its tools its own. -/
def agentInvocation (backend : Backend) (prompt : String) (tools : List String)
    (workdir : System.FilePath) : Invocation :=
  match backend.harness with
  | .claudeCode =>
    let list := ",".intercalate tools
    { cmd := "claude"
      args := #["-p", "--safe-mode", "--tools", list, "--allowedTools", list,
        "--no-session-persistence", "--model", backend.model, "--output-format", "json", "--",
        prompt]
      cwd := workdir }
  | .codex =>
    { cmd := "codex"
      args := #["exec", "--skip-git-repo-check", "--ephemeral", "--sandbox", "workspace-write",
        "-C", workdir.toString, "-m", backend.model, "--", prompt]
      cwd := workdir }

/-- Set by the test driver first thing: a live run while it is set is refused, so no test reaches a
model. -/
initialize liveCallsForbidden : IO.Ref Bool ← IO.mkRef false

/-- The runner that starts real processes. It refuses while the test driver runs, writes the
invocation's files, waits at most `timeoutMs`, kills an overrun and reads back the named files. -/
def liveRunner : Runner := fun inv readBack timeoutMs => do
  if ← liveCallsForbidden.get then
    throw (IO.userError s!"a live call to `{inv.cmd}` during the tests")
  IO.FS.createDirAll inv.cwd
  for (name, text) in inv.files do
    IO.FS.writeFile (inv.cwd / name) text
  let start ← IO.monoMsNow
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := inv.cmd
    args := inv.args
    cwd := some inv.cwd
    stdin := .null
    stdout := .piped
    stderr := .piped }
  let child ← IO.Process.spawn spawnArgs
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  -- Polls every 20 ms; `fuel` bounds the polls so the loop ends even if the clock stalls.
  let rec waitFor : Nat → IO (Option UInt32)
    | 0 => do
      child.kill
      let _ ← child.wait
      return none
    | fuel + 1 => do
      match ← child.tryWait with
      | some code => return some code
      | none =>
        if (← IO.monoMsNow) - start ≥ timeoutMs then waitFor 0
        else
          IO.sleep 20
          waitFor fuel
  match ← waitFor (timeoutMs / 20 + 2) with
  | none => return none
  | some code =>
    let out ← IO.ofExcept stdout.get
    let err ← IO.ofExcept stderr.get
    let mut files := []
    for name in readBack do
      if ← (inv.cwd / name).pathExists then
        files := files ++ [(name, ← IO.FS.readFile (inv.cwd / name))]
    let millis := (← IO.monoMsNow) - start
    let ran : Ran := { exitCode := code, stdout := out, stderr := err, readBack := files, millis }
    return some ran

end SpecTools.Model
