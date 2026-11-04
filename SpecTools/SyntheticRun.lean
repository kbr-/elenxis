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

def ledgerTools : String :=
  "Work through the spec tools on this directory: run `./check.sh audit` (the ledger's audit) and \
  `./check.sh tests` (the ledger's tests against loans.py: which named tests are missing, and \
  which guards no test notices) first and read their findings, then `./check.sh gaps` (a model's \
  proposed gaps between the prose and the ledger) and, if you need them, `./check.sh clauses` (the \
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
def toolsIntro : String :=
  "The spec tools ran on this directory before you started; their reports follow (the audit's \
  verdicts other than proved rows, `tests`' findings, `gaps`' proposals). Check each against the \
  files before you report it, and look past them: a tool can miss a gap and propose a false one. \
  You may rerun them with `./check.sh audit|tests|gaps`."

/-- An arm's prompt; `reports` is the tools arm's tool output, empty for the others. -/
def Arm.prompt (arm : Arm) (reports : String := "") : String := match arm with
  | .baseline => task ++ "\n\n" ++ answerFormat
  | .ledger => task ++ "\n\n" ++ ledgerTools ++ "\n\n" ++ answerFormat
  | .workflow => task ++ "\n\n" ++ workflowOnly ++ "\n\n" ++ answerFormat
  | .tools => task ++ "\n\n" ++ toolsIntro ++ "\n\n" ++ reports ++ "\n\n" ++ answerFormat

/-- The audit's report without its proved rows and their statements, which the files hold. -/
def auditDigest (out : String) : String :=
  "\n".intercalate ((out.splitOn "\n").filter fun l =>
    !(l.startsWith "proved: ") && !(l.startsWith "  ") && l ≠ "")

def checkScript (root : String) (model : String) : String :=
  "\n".intercalate [
    "#!/bin/sh",
    "# The spec tools on this directory: ./check.sh audit | tests | gaps | clauses",
    "D=$(cd \"$(dirname \"$0\")\" && pwd)",
    "echo \"$1\" >> \"$D/check.log\"",
    s!"cd {root} || exit 1",
    "case \"$1\" in",
    "  audit) exec lake env lean \"$D/Loans.lean\" ;;",
    s!"  tests) SPEC_TOOLS_GUARD_WORKERS=3 SPEC_TOOLS_TESTS=1 SPEC_TOOLS_DIR=\"$D\" SPEC_TOOLS_ADAPTER={root}/adapters/python_guards.py exec lake env lean \"$D/Loans.lean\" ;;",
    s!"  gaps) SPEC_TOOLS_GAPS={model} SPEC_TOOLS_DIR=\"$D\" exec lake env lean \"$D/Loans.lean\" ;;",
    s!"  clauses) exec {root}/.lake/build/bin/spec-tools clauses claude-code {model} \"$D/loans.md\" ;;",
    "  *) echo \"usage: ./check.sh audit|tests|gaps|clauses\"; exit 2 ;;",
    "esac", ""]

def findingsOf (j : Json) : Option (List Finding) := do
  let arr ← (j.getObjValAs? (Array Json) "findings").toOption
  arr.toList.mapM fun f => do
    let clause ← (f.getObjValAs? String "clause").toOption
    let kind ← (f.getObjValAs? String "kind").toOption
    return { clause, kind }

/-- The tools of an arm: reading and the tests for all, `./check.sh` for the ledger's and the tools
arm. -/
def armTools (arm : Arm) : List String :=
  ["Read", "Glob", "Grep", "Bash(python3 -m pytest *)"] ++
    (if arm == .ledger || arm == .tools then ["Bash(./check.sh *)"] else [])

/-- One arm's run on one variant: its findings, its cost and the `check.sh` commands it ran, or why
there are none. -/
def runArm (backend : Backend) (variantDir : System.FilePath) (arm : Arm) (root : String)
    (toolModel : String) (timeoutMs : Nat) :
    IO (Except String (List Finding × Cost × List String)) := do
  let work := (← IO.FS.createTempDir) / "variant"
  IO.FS.createDirAll work
  for f in files do IO.FS.writeFile (work / f) (← IO.FS.readFile (variantDir / f))
  if arm == .ledger || arm == .tools then
    IO.FS.writeFile (work / "check.sh") (checkScript root toolModel)
    discard <| IO.Process.output { cmd := "chmod", args := #["+x", (work / "check.sh").toString] }
  -- The tools arm's reports, run before the agent starts; check.log then records only the
  -- agent's own reruns.
  let reports ← if arm == .tools then do
      let run (c : String) := IO.Process.output
        { cmd := (work / "check.sh").toString, args := #[c], cwd := some work.toString }
      let audit ← run "audit"
      let tests ← run "tests"
      let gaps ← run "gaps"
      if ← (work / "check.log").pathExists then IO.FS.removeFile (work / "check.log")
      pure s!"## audit\n{auditDigest audit.stdout}\n\n## tests\n{tests.stdout}\n\n## gaps\n{gaps.stdout}"
    else pure ""
  let question : Question := { prompt := arm.prompt reports, schema := findingsSchema, timeoutMs }
  let inv := agentInvocation backend question (armTools arm) work
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
