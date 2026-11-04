import SpecTools.Model
import SpecTools.Score

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
  loans.md writes it, or as the ledger row writes it when loans.md lacks it, and `kind` says which \
  gap. Give an empty list when you find none."

/-- The final answer's schema: a list of findings, each a quoted clause and a kind. -/
def findingsSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("findings", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "object"),
        ("properties", Json.mkObj [("clause", Json.mkObj [("type", "string")]),
          ("kind", Json.mkObj [("type", "string")])]),
        ("required", Json.arr #["clause", "kind"]), ("additionalProperties", false)])])]),
    ("required", Json.arr #["findings"]), ("additionalProperties", false)]

/-- The ledger's workflow; `check` is the command running the spec tools on the agent's directory. -/
def ledgerTools (check : String) : String :=
  s!"Work through the spec tools on this directory: run `{check} audit` (the ledger's audit) and \
  `{check} tests` (the ledger's tests against loans.py: which named tests are missing, and \
  which guards no test notices) first and read their findings, then `{check} gaps` (a model's \
  proposed gaps between the prose and the ledger) and, if you need them, `{check} clauses` (the \
  clauses of loans.md, extracted twice). Check each finding against the files before you report \
  it. Each command takes up to a few minutes."

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
  You may rerun them with `{check} audit|tests|gaps`."

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

/-- `lake env lean` on the variant's model, from the tools' root, with `env` set. -/
def leanOn (root dir : String) (env : Array (String × Option String)) : Invocation :=
  ⟨"lake", #["env", "lean", dir ++ "/Loans.lean"], env, root⟩

/-- What `spec-tools check SUB` runs on the variant in `dir`, with the tools in `root` and `model` asked
where a tool asks one; none for a command it doesn't know. -/
def checkInvocation (root dir model sub : String) : Option Invocation :=
  if sub = "audit" then some (leanOn root dir #[])
  else if sub = "tests" then some (leanOn root dir #[("SPEC_TOOLS_GUARD_WORKERS", some "3"),
    ("SPEC_TOOLS_TESTS", some "1"), ("SPEC_TOOLS_DIR", some dir),
    ("SPEC_TOOLS_ADAPTER", some (root ++ "/adapters/python_guards.py"))])
  else if sub = "gaps" then some (leanOn root dir #[("SPEC_TOOLS_GAPS", some model), ("SPEC_TOOLS_DIR", some dir)])
  else if sub = "clauses" then
    some ⟨root ++ "/.lake/build/bin/spec-tools", #["clauses", "claude-code", model, dir ++ "/loans.md"], #[], root⟩
  else none

theorem check_unknown_refused (root dir model sub : String)
    (h : sub ≠ "audit" ∧ sub ≠ "tests" ∧ sub ≠ "gaps" ∧ sub ≠ "clauses") :
    checkInvocation root dir model sub = none := by
  obtain ⟨a, t, g, c⟩ := h
  simp [checkInvocation, a, t, g, c]

/-- Only `gaps` and `clauses` ask a model, and each asks the configured one. -/
theorem check_model_is_configured (root dir model : String) :
    (checkInvocation root dir model "gaps").map (·.env) =
      some #[("SPEC_TOOLS_GAPS", some model), ("SPEC_TOOLS_DIR", some dir)] ∧
    (checkInvocation root dir model "clauses").map (·.args) =
      some #["clauses", "claude-code", model, dir ++ "/loans.md"] := by
  simp [checkInvocation, leanOn]

/-- The variant directory's configuration, written by `runArm`: the tools' root and the model their
questions go to, so the agent running `check` chooses neither. -/
def configFile : String := "spec-tools.json"

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
  let child ← IO.Process.spawn { cmd := inv.cmd, args := inv.args, env := inv.env, cwd := some inv.cwd }
  child.wait

def findingsOf (j : Json) : Option (List Finding) := do
  let arr ← (j.getObjValAs? (Array Json) "findings").toOption
  arr.toList.mapM fun f => do
    let clause ← (f.getObjValAs? String "clause").toOption
    let kind ← (f.getObjValAs? String "kind").toOption
    return { clause, kind }

/-- The command an agent runs the spec tools with, the executable in `root`. -/
def checkCommand (root : String) : String := root ++ "/.lake/build/bin/spec-tools check"

/-- The tools of an arm: reading and the tests for all, `spec-tools check` for the ledger's and the
tools arm. -/
def armTools (arm : Arm) (root : String) : List String :=
  ["Read", "Glob", "Grep", "Bash(python3 -m pytest *)"] ++
    (if arm == .ledger || arm == .tools then [s!"Bash({checkCommand root} *)"] else [])

/-- One arm's run on one variant: its findings, its cost and the `check` commands it ran, or why
there are none. -/
def runArm (backend : Backend) (variantDir : System.FilePath) (arm : Arm) (root : String)
    (toolModel : String) (timeoutMs : Nat) :
    IO (Except String (List Finding × Cost × List String)) := do
  let work := (← IO.FS.createTempDir) / "variant"
  IO.FS.createDirAll work
  for f in files do IO.FS.writeFile (work / f) (← IO.FS.readFile (variantDir / f))
  if arm == .ledger || arm == .tools then
    IO.FS.writeFile (work / configFile)
      (Json.mkObj [("root", Json.str root), ("model", Json.str toolModel)]).compress
  -- The tools arm's reports, run before the agent starts; check.log then records only the
  -- agent's own reruns.
  let reports ← if arm == .tools then do
      let run (c : String) := IO.Process.output
        { cmd := root ++ "/.lake/build/bin/spec-tools", args := #["check", c], cwd := some work.toString }
      let audit ← run "audit"
      let tests ← run "tests"
      let gaps ← run "gaps"
      if ← (work / "check.log").pathExists then IO.FS.removeFile (work / "check.log")
      pure s!"## audit\n{auditDigest audit.stdout}\n\n## tests\n{tests.stdout}\n\n## gaps\n{gaps.stdout}"
    else pure ""
  let question : Question :=
    { prompt := arm.prompt (checkCommand root) reports, schema := findingsSchema, timeoutMs }
  let inv := agentInvocation backend question (armTools arm root) work
  let ran ← liveRunner inv (readBackFiles backend.harness) timeoutMs
  let log := work / "check.log"
  let logText ← if ← log.pathExists then IO.FS.readFile log else pure ""
  let checks := (logText.splitOn "\n").filter (· ≠ "")
  match finish backend question ran with
  | .error f => return .error (repr f).pretty
  | .ok o => match findingsOf o.answer with
    | some fs => return .ok (fs, o.cost, checks)
    | none => return .error "the answer has no findings list"

end SpecTools.SyntheticRun
