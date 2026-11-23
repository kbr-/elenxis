import Lean.Data.Json
import SpecTools.Schema
import SpecTools.Usage

/-!
The model interface: the machinery asks a question of a backend and gets back a parsed answer with
its cost, or an error naming the backend. Only the adapters (`invocation`, `readAnswer`) know how a
harness is called; the effects (running a process, timing it) sit in the `Runner` passed in, so tests
script it and no test reaches a model.

Built-in question adapters restrict tools: Claude Code runs with every tool disabled (`--tools ""`) and without the
user's settings, hooks or instructions (`--safe-mode`); Codex runs with `--sandbox read-only`; each
runs in an empty scratch directory. Built-in agent invocations request their harness's tool or
sandbox policy for the working copy (`agentInvocation`).
Command adapters use a versioned JSON file protocol; their executable configuration is trusted and
owns confinement and provider access. The shared planner and schema checker apply to every adapter.
-/

namespace SpecTools.Model
open Lean

inductive Harness where
  | claudeCode
  | codex
  | command (executable : String) (arguments : List String)
  deriving Repr, DecidableEq, Inhabited

def Harness.name : Harness → String
  | .claudeCode => "claude-code"
  | .codex => "codex"
  | .command executable _ => executable

/-- A harness, the model it runs, where the prompt's data goes when it runs, and the reasoning
effort the model is run at (`none`: the harness's own default). -/
structure Backend where
  harness : Harness
  model : String
  dataGoesTo : String
  effort : Option String := none
  deriving Repr, DecidableEq, Inhabited

def Backend.name (b : Backend) : String := s!"{b.harness.name}/{b.model}"

/-- Explain the actual transport; provider provenance never selects another client. -/
def Backend.describe (b : Backend) : String :=
  let effort := match b.effort with
    | some e => s!"; effort {e}"
    | none => ""
  s!"process adapter {b.harness.name}; model {b.model}{effort}; destination note: {b.dataGoesTo}"

/-- A prompt and the JSON Schema its answer must meet, bounded by a timeout. -/
structure Question where
  prompt : String
  schema : Json
  timeoutMs : Nat

/-- Versioned request for an external adapter; no provider protocol leaks into callers. -/
def commandRequest (backend : Backend) (question : Question) (mode : String := "question")
    (tools : List String := []) : Json :=
  Json.mkObj ([("protocol", toJson (1 : Nat)), ("model", toJson backend.model),
    ("prompt", toJson question.prompt), ("schema", question.schema),
    ("timeoutMs", toJson question.timeoutMs), ("mode", toJson mode), ("tools", toJson tools)] ++
    match backend.effort with
    | some e => [("effort", toJson e)]
    | none => [])

/-- An answer and what its call used (`SpecTools.Usage`). -/
structure Outcome where
  answer : Json
  usage : Usage.Usage

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

/-- One process to run: its command, arguments, working directory, and the files
to write into the working directory first. -/
structure Invocation where
  cmd : String
  args : Array String
  cwd : System.FilePath
  files : List (String × String) := []
  input : Option String := none
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

/-- The first `n` non-blank lines of a process's output, for an error message. -/
def firstLines (text : String) (n : Nat := 5) : String :=
  " | ".intercalate ((text.splitOn "\n").filter (!·.trimAscii.isEmpty) |>.take n)

inductive CallMode where
  | question
  | agent (tools : List String)

def CallMode.name : CallMode → String
  | .question => "question"
  | .agent _ => "agent"

def CallMode.tools : CallMode → List String
  | .question => []
  | .agent tools => tools

def callInvocation (backend : Backend) (question : Question) (scratch : System.FilePath)
    (mode : CallMode) : Invocation :=
  match backend.harness with
  | .claudeCode =>
    let toolArgs := match mode with
      | .question => #["--tools", ""]
      | .agent tools =>
        let names := ",".intercalate (tools.map fun t => (t.splitOn "(").headD t).eraseDups
        #["--tools", names, "--allowedTools", " ".intercalate tools]
    let effortArgs := match backend.effort with
      | some e => #["--effort", e]
      | none => #[]
    { cmd := "claude"
      args := #["-p", "--safe-mode"] ++ toolArgs ++ #["--no-session-persistence",
        "--model", backend.model] ++ effortArgs ++ #["--output-format", "json",
        "--json-schema", question.schema.compress, "--", question.prompt]
      cwd := scratch }
  | .codex =>
    let scope := match mode with
      | .question => #["read-only"]
      | .agent _ => #["workspace-write", "-C", scratch.toString]
    let (promptArgs, input) := match mode with
      | .question => (#["-"], some question.prompt)
      | .agent _ => (#["--", question.prompt], none)
    let effortArgs := match backend.effort with
      | some e => #["-c", s!"model_reasoning_effort=\"{e}\""]
      | none => #[]
    { cmd := "codex"
      args := #["exec", "--json", "--skip-git-repo-check", "--ephemeral", "--sandbox"] ++ scope ++ #[
        "-m", backend.model] ++ effortArgs ++ #["--output-schema", "schema.json", "-o",
        "answer.json"] ++ promptArgs
      cwd := scratch
      input := input
      files := [("schema.json", question.schema.compress)] }
  | .command executable arguments =>
    { cmd := executable
      args := (arguments ++ ["request.json"]).toArray
      cwd := scratch
      files := [("request.json", (commandRequest backend question mode.name mode.tools).compress)] }

/-- The command line asking a read-only question in the scratch directory. -/
def invocation (backend : Backend) (question : Question) (scratch : System.FilePath) : Invocation :=
  callInvocation backend question scratch .question

/-- The files the adapter reads back after the run: Codex's answer, a command adapter's optional
usage report. -/
def readBackFiles : Harness → List String
  | .claudeCode => []
  | .codex => ["answer.json"]
  | .command _ _ => ["usage.json"]

/-- What a call used, from whatever its harness reported, whether or not it answered: Claude Code's
JSON report, Codex's `--json` events, a command adapter's `usage.json`; a run that overran reports
nothing, its wall time the limit it was stopped at. -/
def usageOf (backend : Backend) (timeoutMs : Nat) : Option Ran → Usage.Usage
  | none => Usage.unreported timeoutMs
  | some ran => match backend.harness with
    | .claudeCode => match Json.parse ran.stdout with
      | .ok report => Usage.ofClaudeReport report ran.millis
      | .error _ => Usage.unreported ran.millis
    | .codex => Usage.ofCodexEvents ran.stdout ran.millis
    | .command _ _ =>
      Usage.ofAdapterFile ((ran.readBack.lookup "usage.json").bind fun t => (Json.parse t).toOption) ran.millis

/-- The answer a finished run carries, before the schema check. -/
def readAnswer (backend : Backend) (ran : Ran) : Except Failure Json := do
  let name := backend.name
  if ran.exitCode != 0 then
    throw (.exited name ran.exitCode (firstLines (ran.stderr ++ "\n" ++ ran.stdout)))
  match backend.harness with
  | .claudeCode =>
    let report ← (Json.parse ran.stdout).mapError fun e => .malformed name s!"output is no JSON: {e}"
    if (report.getObjValAs? Bool "is_error").toOption == some true then
      throw (.malformed name s!"the harness reported an error: {firstLines ran.stdout}")
    match report.getObjVal? "structured_output" with
    | .ok answer => return answer
    | .error _ => throw (.malformed name "no structured_output in the harness's report")
  | .codex =>
    match ran.readBack.lookup "answer.json" with
    | none => throw (.malformed name "the answer file was not written")
    | some text => (Json.parse text).mapError fun e => .malformed name s!"answer is no JSON: {e}"
  | .command _ _ =>
    (Json.parse ran.stdout).mapError fun e => .malformed name s!"answer is no JSON: {e}"

def routeAllowed (allowed : List Backend) (backend : Backend) : Bool :=
  allowed.any fun candidate =>
    decide (candidate.harness = backend.harness ∧ candidate.model = backend.model)

inductive AttemptStatus where
  | unattempted
  | failed
  | succeeded
  deriving DecidableEq, BEq, Inhabited

inductive EffectDecision where
  | refuse
  | start
  | retry
  | reuse
  deriving DecidableEq, BEq

/-- Decide before scheduling a process. A recorded success can be reused in the same operation. -/
def nextEffect (permitted : Bool) (prior : AttemptStatus) : EffectDecision :=
  if !permitted then .refuse
  else match prior with
    | .unattempted => .start
    | .failed => .retry
    | .succeeded => .reuse

def EffectDecision.schedules : EffectDecision → Bool
  | .start | .retry => true
  | .refuse | .reuse => false

/-- A published success stays authoritative when older failures are replayed. -/
def AttemptStatus.observe (prior : AttemptStatus) (success : Bool) : AttemptStatus :=
  if success || prior == .succeeded then .succeeded else .failed

/-- What to run for `question`, or why nothing may run: a backend the project doesn't allow, a schema
outside the subset, a prompt over `maxPromptBytes`. -/
def plan (allowed : List Backend) (backend : Backend) (question : Question)
    (scratch : System.FilePath) : Except Failure Invocation :=
  if routeAllowed allowed backend = false then
    .error (.refused backend.name "the project doesn't allow this backend")
  else match Schema.unsupported question.schema with
    | some problem => .error (.refused backend.name s!"the question's schema: {problem}")
    | none =>
      if question.prompt.utf8ByteSize > maxPromptBytes then
        .error (.refused backend.name
          s!"the prompt is {question.prompt.utf8ByteSize} bytes, over {maxPromptBytes}")
      else .ok (invocation backend question scratch)

/-- The outcome of a run (`none` when it overran): its answer when it meets the schema. -/
def finish (backend : Backend) (question : Question) : Option Ran → Except Failure Outcome
  | none => .error (.timedOut backend.name question.timeoutMs)
  | some ran => do
    let answer ← readAnswer backend ran
    match Schema.violation question.schema answer with
    | some why => throw (.malformed backend.name s!"answer breaks the schema at {why}")
    | none => return { answer, usage := usageOf backend question.timeoutMs (some ran) }

/-- Ask `question` of `backend` through `runner`, in the empty directory `scratch`: the outcome, and
what the call used whether or not it answered (nothing, for a call refused before running). -/
def askWithUsage (runner : Runner) (allowed : List Backend) (backend : Backend) (question : Question)
    (scratch : System.FilePath) : IO (Except Failure Outcome × Usage.Usage) :=
  match plan allowed backend question scratch with
  | .error failure => pure (.error failure, {})
  | .ok inv => do
    let ran ← runner inv (readBackFiles backend.harness) question.timeoutMs
    return (finish backend question ran, usageOf backend question.timeoutMs ran)

/-- Ask `question` of `backend` through `runner`, in the empty directory `scratch`; an answer carries
its usage, which `askWithUsage` also gives for a call that failed. -/
def ask (runner : Runner) (allowed : List Backend) (backend : Backend) (question : Question)
    (scratch : System.FilePath) : IO (Except Failure Outcome) :=
  match plan allowed backend question scratch with
  | .error failure => pure (.error failure)
  | .ok inv => do
    return finish backend question (← runner inv (readBackFiles backend.harness) question.timeoutMs)

/-- An agent run: `question` given to `backend` working in `workdir` (a copy made for the run), able
to use only `tools`, each a tool name or a pattern such as `Bash(spec-tools check *)`, its final answer
under the question's schema, read back as a question's is (`finish`). Claude Code gets the tools
those name and allows exactly the patterns; Codex gets a sandbox that writes only in `workdir`, its
tools its own. -/
def agentInvocation (backend : Backend) (question : Question) (tools : List String)
    (workdir : System.FilePath) : Invocation :=
  callInvocation backend question workdir (.agent tools)

/-- Set by the test driver first thing: a live run while it is set is refused, so no test reaches a
model. -/
initialize liveCallsForbidden : IO.Ref Bool ← IO.mkRef false

/-- A word quoted for a POSIX shell: in single quotes, each single quote written `'\''`. -/
def shellQuote (s : String) : String := "'" ++ s.replace "'" "'\\''" ++ "'"

/-- The command line an invocation runs on another host: in a directory at the same path, made
first, its words quoted. -/
def remoteCommand (inv : Invocation) : String :=
  let dir := shellQuote inv.cwd.toString
  s!"mkdir -p {dir} && cd {dir} && " ++ " ".intercalate ((inv.cmd :: inv.args.toList).map shellQuote)

/-- A question's command on another host: `remoteCommand`, then its directory and the parents
`mkdir -p` made removed when empty (a question writes no file there; `rmdir` stops at a directory
that isn't empty, such as `/tmp`), the command's exit status kept. -/
def questionCommand (inv : Invocation) : String :=
  s!"{remoteCommand inv}; s=$?; cd / && rmdir -p --ignore-fail-on-non-empty \
    {shellQuote inv.cwd.toString} 2>/dev/null; exit $s"

/-- The script an agent run follows on another host: its working directory (a copy it only reads)
mirrored there by rsync, the harness run in the mirror, the mirror removed, the harness's exit
status kept. -/
def agentScript (host : String) (inv : Invocation) : String :=
  let dir := inv.cwd.toString
  -- The parents `mkdir -p` made are removed too when left empty; rmdir stops at one that isn't.
  let parent := (inv.cwd.parent.getD "/tmp").toString
  let ssh (cmd : String) := s!"ssh -o BatchMode=yes {shellQuote host} {shellQuote cmd}"
  s!"{ssh s!"mkdir -p {shellQuote dir}"} && rsync -a --delete {shellQuote (dir ++ "/")} \
    {shellQuote s!"{host}:{dir}/"} && {ssh (remoteCommand inv)}; s=$?; \
    {ssh s!"rm -rf {shellQuote dir}; rmdir -p --ignore-fail-on-non-empty {shellQuote parent}"}; \
    exit $s"

/-- An invocation run on `host` through ssh (`SPEC_TOOLS_HOST`). A question runs in a directory at
the same path; an agent run (`--allowedTools`) in a mirror of its copy (`agentScript`), which must
lie under `/tmp`, since the mirror is removed after. A call that writes files or reads any back
would find them on the wrong host, so it is refused. -/
def onHost (host : String) (inv : Invocation) (readBack : List String) : Except String Invocation :=
  if !inv.files.isEmpty || !readBack.isEmpty then
    .error s!"SPEC_TOOLS_HOST={host} runs calls that answer on standard output only, and this \
      one exchanges files"
  else if inv.args.contains "--allowedTools" then
    if inv.cwd.toString.startsWith "/tmp/" then
      .ok { inv with cmd := "sh", args := #["-c", agentScript host inv] }
    else .error s!"SPEC_TOOLS_HOST={host} mirrors an agent's copy only under /tmp, and this one \
      is in {inv.cwd}"
  else .ok { inv with cmd := "ssh", args := #["-o", "BatchMode=yes", host, questionCommand inv] }

private def codexCallbackArgs (inv : Invocation) : Array String :=
  let flags := #["exec", "--ignore-user-config", "--disable", "apps"]
  let questionFlags := if inv.input.isSome then
    #["--disable", "shell_tool", "-c", "developer_instructions=" ++
      (toJson ("You are Elenxis's stateless text callback. Use no tools. " ++
        "Answer the supplied question according to its output schema.")).compress]
    else #[]
  flags ++ questionFlags ++ inv.args.extract 1 inv.args.size

private def temporaryCodexPath (path : String) : Bool :=
  path.startsWith "/tmp/" && ((path.splitOn "/").drop 2).all
    (fun component => component != "" && component != "." && component != "..")

/-- Send the schema or the agent's working copy, preserving stdout for usage and collecting only
the structured answer. The remote directory is owned only after successful creation. -/
def codexOnHost (host : String) (home : Option String) (inv : Invocation)
    (timeoutMs : Nat) : Except String Invocation := do
  let dir := inv.cwd.toString
  unless temporaryCodexPath dir && !host.isEmpty && !host.startsWith "-" && !host.contains ':' do
    throw "remote Codex requires an SSH host and an isolated directory under /tmp"
  let ssh (cmd : String) :=
    s!"ssh -o BatchMode=yes -o ConnectTimeout=5 -- {shellQuote host} {shellQuote cmd}"
  let parent := (inv.cwd.parent.getD "/tmp").toString
  let remote := host ++ ":" ++ dir ++ "/"
  let source := if inv.input.isSome then dir ++ "/schema.json" else dir ++ "/"
  let envArgs := (home.toArray.map ("CODEX_HOME=" ++ ·))
  let launch := remoteCommand { inv with
    cmd := "timeout"
    args := #[toString ((timeoutMs + 999) / 1000), "env"] ++ envArgs ++ #["codex"] ++ inv.args }
  let transfer := "rsync -rs -e 'ssh -o BatchMode=yes -o ConnectTimeout=5' --"
  let create := ssh s!"mkdir -p -- {shellQuote parent} && mkdir -m 700 -- {shellQuote dir}"
  let clean := ssh s!"rm -rf -- {shellQuote dir}; rmdir --ignore-fail-on-non-empty -- {shellQuote parent}"
  let upload := s!"{transfer} {shellQuote source} {shellQuote remote}"
  let download := s!"{transfer} {shellQuote (remote ++ "answer.json")} {shellQuote dir}"
  let script := s!"{create} </dev/null || exit $?; trap {shellQuote (clean ++ " </dev/null")} EXIT; \
    {upload} </dev/null && {ssh launch} && {download} </dev/null"
  return { inv with cmd := "sh", args := #["-c", script] }

theorem codexOnHost_refuses_parentTraversal :
    (codexOnHost "model-host" none { cmd := "codex", args := #[], cwd := "/tmp/a/../b" } 1000).toOption.isNone =
      true := by native_decide

/-- The runner that starts real processes. It refuses while the test driver runs, sends a question
to `SPEC_TOOLS_HOST` when set (`onHost`), writes the invocation's files, waits at most
`timeoutMs`, kills an overrun and reads back the named files. -/
def liveRunner : Runner := fun inv readBack timeoutMs => do
  if ← liveCallsForbidden.get then
    throw (IO.userError s!"a live call to `{inv.cmd}` during the tests")
  let inv := if inv.cmd == "codex" && inv.args[0]? == some "exec" then
    { inv with args := codexCallbackArgs inv }
    else inv
  let inv ← match ← IO.getEnv "SPEC_TOOLS_HOST" with
    | some host =>
      let route ← if inv.cmd == "codex" && readBack == ["answer.json"] then
        pure (codexOnHost host (← IO.getEnv "CODEX_HOME") inv timeoutMs)
      else pure (onHost host inv readBack)
      IO.ofExcept (route.mapError IO.userError)
    | none => pure inv
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
  let (child, writer) ← match inv.input with
    | none => pure (← IO.Process.spawn spawnArgs, none)
    | some input => do
      let (stdin, child) ← (← IO.Process.spawn { spawnArgs with stdin := .piped }).takeStdin
      let writer ← IO.asTask (stdin.putStr input *> stdin.flush) .dedicated
      pure (child, some writer)
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
    if code == 0 then
      for task in writer do
        IO.ofExcept task.get
    let mut files := []
    for name in readBack do
      if ← (inv.cwd / name).pathExists then
        files := files ++ [(name, ← IO.FS.readFile (inv.cwd / name))]
    let millis := (← IO.monoMsNow) - start
    let ran : Ran := { exitCode := code, stdout := out, stderr := err, readBack := files, millis }
    return some ran

end SpecTools.Model
