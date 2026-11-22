import SpecTools.UsageReport
import SpecTools.Score
import SpecTools.BackendConfig

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
  | baseline | ledger | workflow | tools
  deriving DecidableEq, Repr

def Arm.name : Arm → String
  | .baseline => "baseline" | .ledger => "ledger" | .workflow => "workflow" | .tools => "tools"

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
  if sub = "audit" then some (leanOn root dir #[])
  else if sub = "tests" then some (leanOn root dir #[("SPEC_TOOLS_GUARD_WORKERS", some "3"),
    ("SPEC_TOOLS_TESTS", some "1"), ("SPEC_TOOLS_DIR", some dir),
    ("SPEC_TOOLS_ADAPTER", some (root ++ "/adapters/python_guards.py"))])
  else if sub = "gaps" then some (leanOn root dir #[("SPEC_TOOLS_GAPS", some model),
    ("SPEC_TOOLS_DIR", some dir), ("SPEC_TOOLS_USAGE", some (usageFile dir))])
  else if sub = "clauses" then
    some ⟨root ++ "/.lake/build/bin/spec-tools", #["clauses", "configured", model, dir ++ "/loans.md"],
      #[("SPEC_TOOLS_USAGE", some (usageFile dir))], root⟩
  else none

theorem check_unknown_refused (root dir model sub : String)
    (h : sub ≠ "audit" ∧ sub ≠ "tests" ∧ sub ≠ "gaps" ∧ sub ≠ "clauses") :
    checkInvocation root dir model sub = none := by
  obtain ⟨a, t, g, c⟩ := h
  simp [checkInvocation, a, t, g, c]

/-- Only `gaps` and `clauses` ask a model; each asks the configured one and records its usage in
the variant's usage file. -/
theorem check_model_is_configured (root dir model : String) :
    (checkInvocation root dir model "gaps").map (·.env) =
      some #[("SPEC_TOOLS_GAPS", some model), ("SPEC_TOOLS_DIR", some dir),
        ("SPEC_TOOLS_USAGE", some (usageFile dir))] ∧
    (checkInvocation root dir model "clauses").map (fun i => (i.args, i.env)) =
      some (#["clauses", "configured", model, dir ++ "/loans.md"],
        #[("SPEC_TOOLS_USAGE", some (usageFile dir))]) := by
  simp [checkInvocation, leanOn]

/-- The variant directory's configuration, written by `runArm`: the tools' root and the model their
questions go to, so the agent running `check` chooses neither. -/
def configFile : String := "spec-tools.json"
private def toolBackendFile : String := "tool-backend.json"

/-- `spec-tools check SUB`, run in a variant's directory: records SUB in `check.log`, then runs the
tool, its output passed through. -/
def runCheck (sub : String) : IO UInt32 := do
  let dir ← IO.currentDir
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
    | IO.eprintln "usage: spec-tools check audit|tests|gaps|clauses"; return 2
  let log ← IO.FS.Handle.mk (dir / "check.log") .append
  log.putStrLn sub
  let toolConfig := dir / toolBackendFile
  let savedBackend ← toolConfig.pathExists
  let passed ← (backendEnvironment.filter (fun k => !savedBackend || k != "SPEC_TOOLS_BACKEND")).filterMapM fun k => do
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

/-- The command an agent runs the spec tools with. -/
def checkCommand (root : String) : String := checkExecutable root ++ " check"

/-- The tools of an arm: reading and the tests for all, `spec-tools check` for the ledger's and the
tools arm. -/
def armTools (arm : Arm) (root : String) : List String :=
  ["Read", "Glob", "Grep", "Bash(python3 -m pytest *)"] ++
    (if arm == .ledger || arm == .tools then [s!"Bash({checkCommand root} *)"] else [])

/-- Run the three preparatory checks. A failed invocation ends preparation with its diagnostic. -/
def prepareReports (executable : String) (work : System.FilePath) : ExceptT String IO String := do
  let run (check : String) : ExceptT String IO String := do
    let result ← liftM <| (IO.Process.output
      { cmd := executable, args := #["check", check], cwd := some work }).toBaseIO
    let output ← match result with
      | .ok output => pure output
      | .error error => throw s!"preparing {check} with {executable}: {error}"
    if output.exitCode != 0 then
      throw s!"preparing {check}: exit {output.exitCode}\n{output.stdout}{output.stderr}"
    return output.stdout
  let audit ← run "audit"
  let tests ← run "tests"
  let gaps ← run "gaps"
  return s!"## audit\n{auditDigest audit}\n\n## tests\n{tests}\n\n## gaps\n{gaps}"

/-- One arm's run on one variant: its findings and the `check` commands it ran, or why there are
none; what its agent used; and what its tools used (the tools arm's reports and every `check` the
agent ran). -/
def runArm (backend : Backend) (variantDir : System.FilePath) (arm : Arm) (root : String)
    (toolBackend : Backend) (timeoutMs : Nat) :
    IO (Except String (List Finding × List String) × Usage.Usage × Usage.Usage) := do
  let work := (← IO.FS.createTempDir) / "variant"
  IO.FS.createDirAll work
  for f in files do IO.FS.writeFile (work / f) (← IO.FS.readFile (variantDir / f))
  if arm == .ledger || arm == .tools then
    IO.FS.writeFile (work / configFile)
      (Json.mkObj [("root", Json.str root), ("model", Json.str toolBackend.model)]).compress
    IO.FS.writeFile (work / toolBackendFile) (backendConfigJson toolBackend).compress
  -- The tools arm's reports, run before the agent starts; check.log then records only the
  -- agent's own reruns.
  let reports ← if arm == .tools then (prepareReports (checkExecutable root) work).run
    else pure (.ok "")
  match reports with
  | .error why => return (.error why, {}, ← Usage.readRecorded (usageFile work.toString))
  | .ok reports =>
    if arm == .tools && (← (work / "check.log").pathExists) then
      IO.FS.removeFile (work / "check.log")
    let question : Question :=
      { prompt := arm.prompt (checkCommand root) reports, schema := findingsSchema, timeoutMs }
    let inv := agentInvocation backend question (armTools arm root) work
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
    return (result, agentUsage, toolsUsage)

end SpecTools.SyntheticRun
