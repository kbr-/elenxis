import SpecTools.UsageReport
import SpecTools.Score
import SpecTools.BackendConfig
import SpecTools.OwnerCheck
import SpecTools.CheckMcp

/-!
The synthetic test's agent runs: each variant given, in a fresh copy, to a fresh agent with the
ledger's tools and to one without (the baseline), each writing its findings to `findings.json`;
the scorer compares both with the key.
-/

namespace SpecTools.SyntheticRun
open Lean SpecTools.Model SpecTools.Score SpecTools.Synthetic

def files : List String := ["loans.md", "Loans.lean", "loans.py", "test_loans.py"]

def task : String :=
  "This directory holds requirements (loans.md), a Lean model of them with a ledger of rows, \
  each a requirement and the theorems establishing it (Loans.lean), a Python implementation \
  (loans.py) and its Hypothesis property tests (test_loans.py). Find every gap between them: a \
  requirement that no Lean statement establishes; a statement weaker than its requirement; a \
  statement whose hypotheses can't hold; a statement of behaviour the requirements don't ask for; \
  a requirement missing from loans.md that the artifacts still decide; a requirement with no test; \
  a test that doesn't check its requirement; and a defect of loans.py. Report only what you find."

def answerFormat : String :=
  "Give your findings as your final answer: for each, `clause` quotes the requirement exactly as \
  loans.md writes it, or as the ledger row writes it when loans.md lacks it, `kind` says which \
  gap, and `row` names the ledger row in Loans.lean of the rule the finding concerns (the rule's \
  own row, such as `r12`, for an exception or a clause the ledger lacks). Give an empty list when \
  you find none."

/-- The final answer's schema: a list of findings, each a quoted clause and a kind. -/
def findingsSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("findings", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "object"),
        ("properties", Json.mkObj [("clause", Json.mkObj [("type", "string")]),
          ("kind", Json.mkObj [("type", "string")]), ("row", Json.mkObj [("type", "string")])]),
        ("required", Json.arr #["clause", "kind", "row"]), ("additionalProperties", false)])])]),
    ("required", Json.arr #["findings"]), ("additionalProperties", false)]

/-- The ledger's workflow; `check` is the command running the spec tools on the agent's directory. -/
def ledgerTools (check : String) : String :=
  s!"Work through the spec tools on this directory: run `{check} audit` (the ledger's audit) and \
  `{check} tests` (the ledger's tests against loans.py: which named tests are missing, and \
  which guards no test notices) first and read their findings, then `{check} gaps` (a model's \
  proposed gaps between the prose and the ledger) and, if you need them, `{check} clauses` (the \
  clauses of loans.md, extracted twice). Check each finding against the files before you report \
  it. Each command takes up to a few minutes: run it in the foreground with a Bash timeout of \
  600000 ms and read its output when it returns, never in the background. Write files only in \
  this directory."

/-- The ledger's workflow with its tools taken out: the prompt-only control, which tells a gain
the prompt gives from one the tools give. -/
def workflowOnly : String :=
  "Work through the requirements clause by clause against the ledger's rows, the Lean statements, \
  loans.py and the tests, in that order. Check each finding against the files before you report it."

/-- The arms: the bare agent; the agent offered the ledger's tools with its workflow; the agent with
the workflow alone; and the agent given the tools' reports, run before it starts. -/
inductive Arm where
  | baseline | ledger | workflow | tools | confirmed
  deriving DecidableEq, Repr

def Arm.name : Arm → String
  | .baseline => "baseline" | .ledger => "ledger" | .workflow => "workflow" | .tools => "tools"
  | .confirmed => "confirmed"

def Arm.preparedChecks : Arm → List String
  | .tools => ["audit", "tests", "gaps"]
  | .confirmed => ["audit", "tests", "gaps", "clauses"]
  | _ => []

/-- What the tools arm is told of the reports it gets. -/
def toolsIntro (check : String) : String :=
  s!"The spec tools ran on this directory before you started; their reports follow (the audit's \
  verdicts other than proved rows, `tests`' findings, `gaps`' proposals). Check each against the \
  files before you report it, and look past them: a tool can miss a gap and propose a false one. \
  You may rerun them with `{check} audit|tests|gaps`, each in the foreground with a Bash timeout \
  of 600000 ms, never in the background; write files only in this directory."

/-- An arm's prompt; `check` is the spec tools' command, `reports` the tools arm's tool output,
empty for the others. -/
def Arm.prompt (arm : Arm) (check : String) (reports : String := "") : String := match arm with
  | .baseline => task ++ "\n\n" ++ answerFormat
  | .ledger => task ++ "\n\n" ++ ledgerTools check ++ "\n\n" ++ answerFormat
  | .workflow => task ++ "\n\n" ++ workflowOnly ++ "\n\n" ++ answerFormat
  | .tools => task ++ "\n\n" ++ toolsIntro check ++ "\n\n" ++ reports ++ "\n\n" ++ answerFormat
  | .confirmed => task ++ "\n\nAudit, tests, gaps and clauses completed before this run. " ++
    "Use their reports to check what the prose requires and what the artifacts establish. " ++
    "Verify each reported finding against the files.\n\n" ++ reports ++ "\n\n" ++ answerFormat

/-- The audit's report without its proved rows and their statements, which the files hold. -/
def auditDigest (out : String) : String :=
  "\n".intercalate ((out.splitOn "\n").filter fun l =>
    !(l.startsWith "proved: ") && !(l.startsWith "  ") && l ≠ "")

/-- A process to run: what `spec-tools check` starts for one of the spec tools on a variant. -/
structure Invocation where
  cmd : String
  args : Array String
  env : Array (String × Option String) := #[]
  cwd : String
  deriving Repr, DecidableEq

/-- The invocation with a `lake env` run's variables, and `passed` (`K=V` words), moved into its
arguments (`lake env env K=V ... CMD`): outside a launcher job the lake proxy runs lake through
compute.sh, whose job inherits no caller environment, so a variable set on the process never
reaches the command. Any other invocation is unchanged. -/
def Invocation.viaArgs (i : Invocation) (passed : List String) : Invocation :=
  if i.cmd = "lake" ∧ i.args[0]? = some "env" then
    let vars := (i.env.filterMap fun (k, v) => v.map (s!"{k}=" ++ ·)) ++ passed.toArray
    ⟨i.cmd, #["env", "env"] ++ vars ++ i.args.extract 1 i.args.size, #[], i.cwd⟩
  else i

theorem viaArgs_moves_env :
    (Invocation.viaArgs ⟨"lake", #["env", "lean", "d/Loans.lean"], #[("A", some "1"), ("B", none)], "r"⟩
      ["H=h"]) = ⟨"lake", #["env", "env", "A=1", "H=h", "lean", "d/Loans.lean"], #[], "r"⟩ ∧
    (Invocation.viaArgs ⟨"tool", #["x"], #[("A", some "1")], "r"⟩ ["H=h"]) =
      ⟨"tool", #["x"], #[("A", some "1")], "r"⟩ := by native_decide

/-- `lake env lean` on the variant's model, from the tools' root, with `env` set. -/
def leanOn (root dir : String) (env : Array (String × Option String)) : Invocation :=
  ⟨"lake", #["env", "lean", dir ++ "/Loans.lean"], env, root⟩

/-- The file in a variant's directory the tools `check` runs record their calls' usage in. -/
def usageFile (dir : String) : String := dir ++ "/usage.jsonl"

/-- What `spec-tools check SUB` runs on the variant in `dir`, with the tools in `root` and `model` asked
where a tool asks one; none for a command it doesn't know. A tool that asks a model records its
usage in `usageFile dir`. -/
def checkInvocation (root dir model sub : String) : Option Invocation :=
  match OwnerCheck.decode sub none with
  | some .audit => some (leanOn root dir #[])
  | some .tests => some (leanOn root dir #[("SPEC_TOOLS_GUARD_WORKERS", some "3"),
    ("SPEC_TOOLS_TESTS", some "1"), ("SPEC_TOOLS_DIR", some dir),
    ("SPEC_TOOLS_ADAPTER", some (root ++ "/adapters/python_guards.py")),
    ("SPEC_TOOLS_REPLAY_ADAPTER", some (root ++ "/adapters/loans_replay.py"))])
  | some .gaps => some (leanOn root dir #[("SPEC_TOOLS_GAPS", some model),
    ("SPEC_TOOLS_DIR", some dir), ("SPEC_TOOLS_USAGE", some (usageFile dir))])
  | some .clauses =>
    some ⟨root ++ "/.lake/build/bin/spec-tools", #["clauses", "configured", model, dir ++ "/loans.md"],
      #[("SPEC_TOOLS_USAGE", some (usageFile dir))], root⟩
  | none => none

theorem check_unknown_refused (root dir model sub : String)
    (h : sub ≠ "audit" ∧ sub ≠ "tests" ∧ sub ≠ "gaps" ∧ sub ≠ "clauses") :
    checkInvocation root dir model sub = none := by
  obtain ⟨a, t, g, c⟩ := h
  unfold checkInvocation
  cases accepted : OwnerCheck.decode sub none with
  | none => rfl
  | some check =>
    have name := ((OwnerCheck.decode_iff sub none check).mp accepted).2
    cases check <;> simp_all [OwnerCheck.Check.name]

/-- Only `gaps` and `clauses` ask a model; each asks the configured one and records its usage in
the variant's usage file. -/
theorem check_model_is_configured (root dir model : String) :
    (checkInvocation root dir model "gaps").map (·.env) =
      some #[("SPEC_TOOLS_GAPS", some model), ("SPEC_TOOLS_DIR", some dir),
        ("SPEC_TOOLS_USAGE", some (usageFile dir))] ∧
    (checkInvocation root dir model "clauses").map (fun i => (i.args, i.env)) =
      some (#["clauses", "configured", model, dir ++ "/loans.md"],
        #[("SPEC_TOOLS_USAGE", some (usageFile dir))]) := by
  have gaps : OwnerCheck.decode "gaps" none = some .gaps := rfl
  have clauses : OwnerCheck.decode "clauses" none = some .clauses := rfl
  simp [checkInvocation, gaps, clauses, leanOn]

/-- The variant directory's configuration, written by `runArm`: the tools' root and the model their
questions go to, so the agent running `check` chooses neither. -/
def configFile : String := "spec-tools.json"
private def toolBackendFile : String := "tool-backend.json"

/-- A Lean project check always selects a fixed local build target. -/
def runProjectCheck (sub : String) : IO UInt32 := do
  let some target := OwnerCheck.projectTargets.lookup sub
    | IO.eprintln "usage: spec-tools check proofs|contracts|counterexamples"; return 2
  let dir ← IO.currentDir
  unless (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) do
    IO.eprintln "check: run from the Lean project's directory"
    return 2
  unless ← (dir / (target ++ ".lean")).pathExists do
    IO.eprintln s!"check: {target}.lean is missing from the Lean project"
    return 2
  let child ← IO.Process.spawn { cmd := "lake", args := #["build", target], cwd := some dir }
  child.wait

/-- A legacy check, run in a variant's directory: records SUB in `check.log`, then runs the
tool, its output passed through. -/
def runLegacyCheck (requested : String) : IO UInt32 := do
  let dir ← IO.currentDir
  let sub := if requested == "integration" then "tests" else requested
  if sub == "tests" then
    unless (← (dir / "Loans.lean").pathExists) && (← (dir / "loans.py").pathExists) &&
        (← (dir / "test_loans.py").pathExists) do
      IO.eprintln "legacy Python integration requires Loans.lean, loans.py and test_loans.py"
      return 2
    IO.println "legacy Python integration"
  unless ← (dir / configFile).pathExists do
    IO.eprintln s!"check: no {configFile} in {dir}; run it in an arm's variant directory, which the run writes"
    return 2
  let .ok cfg := Json.parse (← IO.FS.readFile (dir / configFile))
    | IO.eprintln s!"check: {configFile} in {dir} isn't JSON"; return 2
  let some root := (cfg.getObjValAs? String "root").toOption
    | IO.eprintln s!"check: {configFile} names no root"; return 2
  let some model := (cfg.getObjValAs? String "model").toOption
    | IO.eprintln s!"check: {configFile} names no model"; return 2
  let some inv := checkInvocation root dir.toString model sub
    | IO.eprintln "usage: spec-tools check --target python audit|integration|gaps|clauses"; return 2
  let log ← IO.FS.Handle.mk (dir / "check.log") .append
  log.putStrLn sub
  let toolConfig := dir / toolBackendFile
  let savedBackend ← toolConfig.pathExists
  let names := if sub == "gaps" then
      backendEnvironment ++ ["SPEC_TOOLS_GAP_READINGS", "SPEC_TOOLS_MECHANICAL_GAPS"]
    else backendEnvironment
  let passed ← (names.filter (fun k => !savedBackend || k != "SPEC_TOOLS_BACKEND")).filterMapM fun k => do
    return (← IO.getEnv k).map (s!"{k}=" ++ ·)
  let inv := if savedBackend then
    { inv with env := inv.env.push ("SPEC_TOOLS_BACKEND", some toolConfig.toString) }
    else inv
  let inv := inv.viaArgs passed
  let child ← IO.Process.spawn { cmd := inv.cmd, args := inv.args, env := inv.env, cwd := some inv.cwd }
  child.wait

/-- A finding's row, where the answer gives one: answers saved before rows were asked for have
none, and are scored by their quotes. -/
def findingsOf (j : Json) : Option (List Finding) := do
  let arr ← (j.getObjValAs? (Array Json) "findings").toOption
  arr.toList.mapM fun f => do
    let clause ← (f.getObjValAs? String "clause").toOption
    let kind ← (f.getObjValAs? String "kind").toOption
    return { clause, kind, row := (f.getObjValAs? String "row").toOption }

/-- A finding as a results file saves it: `[clause, kind]`, and its row third where it has one. -/
def savedFinding (f : Finding) : Json :=
  Json.arr (#[Json.str f.clause, Json.str f.kind] ++ (f.row.map fun r => #[Json.str r]).getD #[])

def findingOfSaved (j : Json) : Option Finding := do
  let clause ← (j.getArrVal? 0 >>= Json.getStr?).toOption
  let kind ← (j.getArrVal? 1 >>= Json.getStr?).toOption
  return { clause, kind, row := (j.getArrVal? 2 >>= Json.getStr?).toOption }

example : findingOfSaved (savedFinding ⟨"a", "b", some "r3"⟩) = some ⟨"a", "b", some "r3"⟩ := by
  native_decide
example : findingOfSaved (savedFinding ⟨"a", "b", none⟩) = some ⟨"a", "b", none⟩ := by
  native_decide

/-- Each variant's presentations by rule number, from a batch's `key.jsonl`, by variant number; a
key written before presentations has none. -/
def keyPresentations (keyText : String) : List (Nat × List (Nat × Generated.Presentation)) :=
  (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
    let j ← (Json.parse l).toOption
    let v ← (j.getObjValAs? Nat "variant").toOption
    let ps ← (j.getObjValAs? (Array Json) "presentations").toOption
    let shown ← ps.toList.mapM fun p => do
      let id ← (p.getObjValAs? Nat "rule").toOption
      let name ← (p.getObjValAs? String "presentation").toOption
      let pr ← Generated.Presentation.all.find? (·.name == name)
      return (id, pr)
    return (v, shown)

/-- Each variant's plants, from a batch's `key.jsonl`, one line a variant; a plant's row where the
key gives one. -/
def keyPlants (keyText : String) : List (List Plant) :=
  (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
    let j ← (Json.parse l).toOption
    let plants ← (j.getObjValAs? (Array Json) "plants").toOption
    plants.toList.mapM fun p => do
      return { kind := ← (p.getObjValAs? String "kind").toOption,
               clause := ← (p.getObjValAs? String "clause").toOption, edits := [],
               row := (p.getObjValAs? String "row").toOption }

/-- The executable for checks of a synthetic variant. -/
def checkExecutable (root : String) : String := root ++ "/.lake/build/bin/spec-tools"

/-- Called under the fixture lock by the protected launcher. Record the attempt before starting
the CLI and retain its actual status and both output streams. -/
def runLockedCheck (profile : OwnerCheck.Profile) (sub : String) (receipt : System.FilePath) :
    IO UInt32 := do
  unless OwnerCheck.admitted profile sub none do return 2
  let work ← IO.currentDir
  let executable ← match profile with
    | .project => pure (← IO.appPath).toString
    | .pythonLegacy => do
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (work / configFile)))
      pure (checkExecutable (← IO.ofExcept (json.getObjValAs? String "root")))
  let journal ← IO.FS.Handle.mk (work / "check-events.jsonl") .append
  let event (phase : String) (fields : List (String × Json)) := do
    journal.putStrLn (Json.mkObj ([("check", toJson sub), ("phase", toJson phase)] ++ fields)).compress
    journal.flush
  event "attempt" []
  let result ← (IO.Process.output {
    cmd := executable
    args := (#["check"] ++ profile.options.toArray).push sub
    cwd := some work }).toBaseIO
  let (ok, report) ← match result with
    | .error error => do
      event "failed_to_start" [("error", toJson (toString error))]
      pure (false, toString error)
    | .ok response => do
      event "exit" [("status", toJson response.exitCode.toNat)]
      pure (response.exitCode == 0,
        s!"{sub}: exit {response.exitCode}\n{response.stdout}{response.stderr}")
  IO.FS.writeFile receipt (Json.mkObj [("ok", toJson ok), ("report", toJson report)]).compress
  return 0

/-- Serve fixture checks on the machine holding the original variant and the Lean build. -/
def serveChecks (profile : OwnerCheck.Profile) (launcher executable : String) : IO UInt32 := do
  let work ← IO.currentDir
  let env ← backendEnvironment.filterMapM fun key => do
    return (← IO.getEnv key).map (s!"{key}=" ++ ·)
  CheckMcp.serve profile fun check => do
    let scratch ← IO.FS.createTempDir
    let receipt := scratch / "receipt.json"
    let job ← (IO.Process.output {
      cmd := launcher
      args := #["--category", "formal_verification", "--expect", "60", "env"] ++ env.toArray ++
        #["/usr/bin/flock", (work / "check.lock").toString, executable, "fixture-check"] ++
        profile.options.toArray ++ #[check, receipt.toString]
      cwd := some work }).toBaseIO
    let result ← match job with
      | .error error => pure (false, s!"Could not launch {check}: {error}")
      | .ok job =>
        if job.exitCode == 0 && (← receipt.pathExists) then
          let json ← IO.ofExcept (Json.parse (← IO.FS.readFile receipt))
          pure (← IO.ofExcept (json.getObjValAs? Bool "ok"),
            ← IO.ofExcept (json.getObjValAs? String "report"))
        else pure (false, s!"Check launcher exited {job.exitCode}\n{job.stdout}{job.stderr}")
    IO.FS.removeDirAll scratch
    return result
  return 0

private def remoteLedger (backend : Backend) (arm : Arm) : IO Bool := do
  return backend.harness == .codex && arm == .ledger && (← IO.getEnv "SPEC_TOOLS_HOST").isSome

private def fixtureToolArgs (work : System.FilePath) (root : String) (timeoutMs : Nat) :
    IO (Except String (Array String)) := do
  let host := (← IO.getEnv "SPEC_TOOLS_CHECK_HOST").getD ""
  let launcher := (← IO.getEnv "SPEC_TOOLS_CHECK_LAUNCHER").getD ""
  unless !host.isEmpty && !host.startsWith "-" && !host.contains ':' &&
      (System.FilePath.mk launcher).isAbsolute do
    return .error "Remote Codex ledger requires SPEC_TOOLS_CHECK_HOST and an absolute SPEC_TOOLS_CHECK_LAUNCHER"
  let env ← backendEnvironment.filterMapM fun key => do
    return (← IO.getEnv key).map (s!"{key}=" ++ ·)
  let seconds := (timeoutMs + 999) / 1000
  let executable := checkExecutable root
  let command := s!"cd {shellQuote work.toString} && exec " ++ " ".intercalate
    ((["timeout", toString seconds, "env"] ++ env ++
      [executable, "fixture-mcp", launcher, executable, "--target", "python"]).map shellQuote)
  let args := toJson #["-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "--", host, command]
  let approvals := OwnerCheck.Profile.pythonLegacy.names.toArray.flatMap fun check =>
    #["-c", s!"mcp_servers.elenxis.tools.{check}.approval_mode=\"approve\""]
  return .ok (#["-c", "mcp_servers.elenxis.command=\"/usr/bin/ssh\"",
    "-c", "mcp_servers.elenxis.args=" ++ args.compress, "-c", "mcp_servers.elenxis.required=true",
    "-c", "mcp_servers.elenxis.startup_timeout_sec=10",
    "-c", s!"mcp_servers.elenxis.tool_timeout_sec={seconds}"] ++ approvals)

/-- The command an agent runs the spec tools with. -/
def checkCommand (root : String) : String := checkExecutable root ++ " check --target python"

/-- The tools of an arm: reading and the tests for all, `spec-tools check` for the ledger's and the
tools arm. -/
def armTools (arm : Arm) (root : String) : List String :=
  ["Read", "Glob", "Grep", "Bash(python3 -m pytest *)"] ++
    (if arm == .ledger || !arm.preparedChecks.isEmpty then [s!"Bash({checkCommand root} *)"] else [])

/-- Run the named preparatory checks. A failed invocation ends preparation with its diagnostic. -/
def prepareReports (executable : String) (work : System.FilePath)
    (checks : List String := Arm.tools.preparedChecks) (readings : Nat := 1) :
    ExceptT String IO String := do
  let run (check : String) : ExceptT String IO String := do
    let result ← liftM <| (IO.Process.output
      { cmd := executable, args := #["check", "--target", "python", check], cwd := some work,
        env := #[("SPEC_TOOLS_GAP_READINGS", some (toString readings))] }).toBaseIO
    let output ← match result with
      | .ok output => pure output
      | .error error => throw s!"preparing {check} with {executable}: {error}"
    if output.exitCode != 0 then
      throw s!"preparing {check}: exit {output.exitCode}\n{output.stdout}{output.stderr}"
    let report := if check == "audit" then auditDigest output.stdout else output.stdout
    return s!"## {check}\n{report}"
  return String.intercalate "\n\n" (← checks.mapM run)

/-- One arm's run on one variant: its findings and the `check` commands it ran, or why there are
none; what its agent used; and what its tools used (the tools arm's reports and every `check` the
agent ran). -/
def runArm (backend : Backend) (variantDir : System.FilePath) (arm : Arm) (root : String)
    (toolBackend : Backend) (timeoutMs : Nat) :
    IO (Except String (List Finding × List String) × Usage.Usage × Usage.Usage × Array Json) := do
  let work := (← IO.FS.createTempDir) / "variant"
  let bound ← remoteLedger backend arm
  let transport ← if bound then fixtureToolArgs work root timeoutMs else pure (.ok #[])
  let .ok toolArgs := transport | return (transport.map (fun _ => ([], [])), {}, {}, #[])
  IO.FS.createDirAll work
  for f in files do IO.FS.writeFile (work / f) (← IO.FS.readFile (variantDir / f))
  if arm == .ledger || !arm.preparedChecks.isEmpty then
    IO.FS.writeFile (work / configFile)
      (Json.mkObj [("root", Json.str root), ("model", Json.str toolBackend.model)]).compress
    IO.FS.writeFile (work / toolBackendFile) (backendConfigJson toolBackend).compress
  -- The tools arm's reports, run before the agent starts; check.log then records only the
  -- agent's own reruns.
  let readings := if arm == .confirmed then 3 else 1
  let structuredRequirements := "prose-rules.json"
  let hasStructuredRequirements ←
    (variantDir / structuredRequirements).pathExists
  let copyRequirements := arm == .confirmed && hasStructuredRequirements
  if copyRequirements then
    IO.FS.writeFile (work / structuredRequirements)
      (← IO.FS.readFile (variantDir / structuredRequirements))
  let reports ← try
    (prepareReports (checkExecutable root) work arm.preparedChecks readings).run
  finally
    if copyRequirements then IO.FS.removeFile (work / structuredRequirements)
  match reports with
  | .error why => return (.error why, {}, ← Usage.readRecorded (usageFile work.toString), #[])
  | .ok reports =>
    if !arm.preparedChecks.isEmpty && (← (work / "check.log").pathExists) then
      IO.FS.removeFile (work / "check.log")
    let prompt := if bound then task ++ "\n\n" ++
      "Use the Elenxis MCP tools on the fixture. Audit checks proof status, integration checks the \
      named tests, gaps compares prose to the ledger and clauses extracts the prose's claims. Select \
      checks as needed. Verify each finding against the files.\n\n" ++ answerFormat
      else arm.prompt (checkCommand root) reports
    let question : Question := { prompt, schema := findingsSchema, timeoutMs }
    let inv := agentInvocation backend question (armTools arm root) work
    let inv := { inv with args := (inv.args.extract 0 1) ++ toolArgs ++ inv.args.extract 1 inv.args.size }
    let ran ← liveRunner inv (readBackFiles backend.harness) timeoutMs
    let log := work / "check.log"
    let logText ← if ← log.pathExists then IO.FS.readFile log else pure ""
    let checks := (logText.splitOn "\n").filter (· ≠ "")
    let agentUsage := usageOf backend timeoutMs ran
    let toolsUsage ← Usage.readRecorded (usageFile work.toString)
    let result := match finish backend question ran with
      | .error f => .error (repr f).pretty
      | .ok o => match findingsOf o.answer with
        | some fs => .ok (fs, checks)
        | none => .error "the answer has no findings list"
    let eventPath := work / "check-events.jsonl"
    let events ← if ← eventPath.pathExists then
      pure <| ((← IO.FS.readFile eventPath).splitOn "\n").toArray.filterMap
        (fun line => (Json.parse line).toOption)
      else pure #[]
    return (result, agentUsage, toolsUsage, events)

end SpecTools.SyntheticRun
