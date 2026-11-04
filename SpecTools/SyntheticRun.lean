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

def checkScript (root : String) (model : String) : String :=
  "\n".intercalate [
    "#!/bin/sh",
    "# The spec tools on this directory: ./check.sh audit | tests | gaps | clauses",
    "D=$(cd \"$(dirname \"$0\")\" && pwd)",
    "echo \"$1\" >> \"$D/check.log\"",
    s!"cd {root} || exit 1",
    "case \"$1\" in",
    "  audit) exec lake env lean \"$D/Loans.lean\" ;;",
    s!"  tests) SPEC_TOOLS_TESTS=1 SPEC_TOOLS_DIR=\"$D\" SPEC_TOOLS_ADAPTER={root}/adapters/python_guards.py exec lake env lean \"$D/Loans.lean\" ;;",
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

/-- The tools of an arm: reading and the tests for both, `./check.sh` for the ledger's. -/
def armTools (ledger : Bool) : List String :=
  ["Read", "Glob", "Grep", "Bash(python3 -m pytest *)"] ++
    (if ledger then ["Bash(./check.sh *)"] else [])

/-- One arm's run on one variant: its findings, its cost and the `check.sh` commands it ran, or why
there are none. -/
def runArm (backend : Backend) (variantDir : System.FilePath) (ledger : Bool) (root : String)
    (toolModel : String) (timeoutMs : Nat) :
    IO (Except String (List Finding × Cost × List String)) := do
  let work := (← IO.FS.createTempDir) / "variant"
  IO.FS.createDirAll work
  for f in files do IO.FS.writeFile (work / f) (← IO.FS.readFile (variantDir / f))
  if ledger then
    IO.FS.writeFile (work / "check.sh") (checkScript root toolModel)
    discard <| IO.Process.output { cmd := "chmod", args := #["+x", (work / "check.sh").toString] }
  let question : Question :=
    { prompt := task ++ "\n\n" ++ (if ledger then ledgerTools ++ "\n\n" else "") ++ answerFormat,
      schema := findingsSchema, timeoutMs }
  let inv := agentInvocation backend question (armTools ledger) work
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
