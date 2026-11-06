import SpecTools

/-!
Tests of what meets the world: the live runner starting real processes. The pure core's properties
are theorems (`SpecTools.ModelProofs`).
-/

open SpecTools.Model

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.FS.createTempDir) / name
  IO.FS.createDirAll dir
  return dir

/-- A process that exits is read back whole: status, output, the files it wrote. -/
def testFinishedProcess : IO Unit := do
  let dir ← scratch "finished"
  let inv : Invocation := {
    cmd := "sh"
    args := #["-c", "cat in.txt > out.txt; echo said; exit 3"]
    cwd := dir
    files := [("in.txt", "written first")] }
  match ← liveRunner inv ["out.txt", "absent.txt"] 10000 with
  | none => throw <| IO.userError "a quick process was reported as an overrun"
  | some ran =>
    ensure (ran.exitCode == 3) s!"exit status {ran.exitCode}, expected 3"
    ensure (ran.stdout == "said\n") s!"stdout {ran.stdout.quote}"
    ensure (ran.readBack == [("out.txt", "written first")])
      "the invocation's file was written before the run and the run's file read back, an absent one skipped"

/-- A process past its limit is killed and reported as an overrun, without waiting for it. -/
def testOverrun : IO Unit := do
  let dir ← scratch "overrun"
  let start ← IO.monoMsNow
  let result ← liveRunner { cmd := "sleep", args := #["30"], cwd := dir } [] 300
  let elapsed := (← IO.monoMsNow) - start
  ensure result.isNone "an overrun gives no result"
  ensure (elapsed < 5000) s!"the overrun was waited out for {elapsed} ms"

/-- Run the audit over a Lean file written for the case, in this project's environment. -/
def auditCase (dir : System.FilePath) (name body : String) : IO (UInt32 × String) := do
  let file := dir / s!"{name}.lean"
  IO.FS.writeFile file ("import SpecTools.Audit\nimport SpecTools.GapsRun\nopen SpecTools.Ledger\n" ++ body)
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", file.toString] }
  return (out.exitCode, out.stdout ++ out.stderr)

def has (text needle : String) : Bool := (text.splitOn needle).length > 1

/-- The audit reads the environment: missing names, unclaimed theorems, axioms, hypotheses without
witnesses, and the digests that skip unchanged rows. -/
def testAudit : IO Unit := do
  let dir ← IO.FS.createTempDir
  let digest := dir / "digests.txt"
  let base := "theorem plain : 1 + 1 = 2 := rfl\n\
    theorem guarded (n : Nat) (h : 0 < n) : n ≠ 0 := by omega\n\
    theorem witness : (0 < 1) := by decide\n"
  let rows (clause : String) := s!"#eval SpecTools.Audit.run [
    \{ id := \"r1\", clause := \"{clause}\", theorems := [``plain] },
    \{ id := \"r2\", clause := \"guarded\", theorems := [``guarded], witnesses := [``witness] }]
    `AuditCase (digestFile := some \"{digest}\")\n"
  -- The cases reading no digests run beside the three that share the digest file, in order.
  let missing ← IO.asTask <| auditCase dir "missing" (base ++ "#eval SpecTools.Audit.run [
    { id := \"r1\", clause := \"c\", theorems := [`nonexistent, ``plain, ``guarded], witnesses := [``witness] }] `AuditCase\n")
  let unclaimedCase ← IO.asTask <| auditCase dir "unclaimed" (base ++ "#eval SpecTools.Audit.run [
    { id := \"r1\", clause := \"c\", theorems := [``plain] }] `AuditCase\n")
  let axiomCase ← IO.asTask <| auditCase dir "axiom" ("axiom myAxiom : 1 = 1\ntheorem leans : 1 = 1 := myAxiom\n\
    #eval SpecTools.Audit.run [{ id := \"r1\", clause := \"c\", theorems := [``leans] }] `AuditCase\n")
  let vacuous ← IO.asTask <| auditCase dir "vacuous" ("theorem guarded (n : Nat) (h : 0 < n) : n ≠ 0 := by omega\n\
    #eval SpecTools.Audit.run [{ id := \"r1\", clause := \"c\", theorems := [``guarded] }] `AuditCase\n")
  let (code, out) ← auditCase dir "pass" (base ++ rows "one plus one")
  ensure (code == 0 && has out "proved: r1" && has out "proved: r2" &&
      has out "2 rows: 2 proved, 0 conditional, 0 too weak or vacuous, 0 not stated (2 judged)")
    s!"a complete ledger passes, both rows proved:\n{out}"
  let (code, out) ← auditCase dir "again" (base ++ rows "one plus one")
  ensure (code == 0 && has out "unchanged: r1" && has out "(0 judged)")
    s!"a second run with nothing changed judges no row:\n{out}"
  let (code, out) ← auditCase dir "changed" (base ++ rows "one and one")
  ensure (code == 0 && has out "unchanged: r2" && has out "proved: r1" && has out "(1 judged)")
    s!"a changed clause re-judges that row alone:\n{out}"
  let (code, out) ← IO.ofExcept missing.get
  ensure (code != 0 && has out "names nonexistent, which is no theorem")
    s!"a row naming no theorem fails the audit:\n{out}"
  let (code, out) ← IO.ofExcept unclaimedCase.get
  ensure (code != 0 && has out "no row claims theorem guarded")
    s!"a written theorem no row claims fails the audit:\n{out}"
  let (code, out) ← IO.ofExcept axiomCase.get
  ensure (code == 0 && has out "conditional: r1" && has out "axioms: [myAxiom]")
    s!"an axiom outside the accepted three makes the row conditional:\n{out}"
  let (code, out) ← IO.ofExcept vacuous.get
  ensure (code == 0 && has out "too weak or vacuous: r1")
    s!"hypotheses without a witness are reported:\n{out}"

def testRequirementAudits : IO Unit := IO.FS.withTempDir fun dir => do
  let cases : List (String × String × Bool × List String) := [
    ("Requirement", "def obligation (n : Nat) : Prop := n + 0 = n\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `Requirement (requirements := true)\n", true, ["specified (unproved): r", "n + 0 = n"]),
    ("ProofOnly", "def obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `ProofOnly\n", false, ["which is no theorem"]),
    ("WrongType", "def notAProperty : Nat := 4\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``notAProperty] }] \
      `WrongType (requirements := true)\n", false, ["not a proposition"]),
    ("MissingRequirement", "#eval SpecTools.Audit.run \
      [{ id := \"r\", clause := \"identity\", theorems := [`absent] }] \
      `MissingRequirement (requirements := true)\n", false, ["names absent"]),
    ("EmptyRequirements", "#eval SpecTools.Model.liveCallsForbidden.set true\n\
      #eval SpecTools.Gaps.run [] \"\" \
      { harness := .codex, model := \"must-not-run\", dataGoesTo := \"forbidden\" } (requirements := true)\n",
      false, ["specification ledger is empty"]),
    ("UntrustedRequirement", "axiom untrusted : Prop\ndef obligation : Prop := untrusted\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `UntrustedRequirement (requirements := true)\n", false, ["conditional"]),
    ("OpaqueRequirement", "opaque obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `OpaqueRequirement (requirements := true)\n", false, ["safe requirement body"]),
    ("UnsafeRequirement", "unsafe def obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `UnsafeRequirement (requirements := true)\n", false, ["safe requirement body"]),
    ("MultipleInvalidRequirements", "def notAProperty : Nat := 4\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", \
      theorems := [`absent, ``notAProperty] }] `MultipleInvalidRequirements (requirements := true)\n",
      false, ["names absent", "notAProperty is not a proposition"]),
    ("UnprovedWitness", "theorem guarded (h : False) : False := h\ndef witness : Prop := False\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", \
      theorems := [``guarded], witnesses := [``witness] }] `UnprovedWitness (requirements := true)\n",
      false, ["witness witness is not proved"])]
  let running ← cases.mapM fun (name, body, passes, messages) => do
    let task ← IO.asTask (auditCase dir name body)
    return (name, passes, messages, task)
  for (name, passes, messages, task) in running do
    let (code, output) ← IO.ofExcept task.get
    ensure ((code == 0) == passes && messages.all (has output)) s!"{name}: {output}"
  IO.println "PASS: requirement audit (unproved, proof-only, wrong type, missing, empty, untrusted, opaque, unsafe, all findings, witness)"

/-- Real process boundary: literal prompts survive the request file, and malformed/schema-breaking
responses and nonzero exits cannot become successful answers. No model or provider is contacted. -/
def testCommandAdapter : IO Unit := do
  let dir ← IO.FS.createTempDir
  let backend : Backend := { harness := .command "cat" [], model := "local/model", dataGoesTo := "local" }
  let schema := Lean.Json.mkObj [("type", "object")]
  for prompt in ["", "Zażółć\n\"quotes\" $(literal) \\ path"] do
    let question : Question := { prompt, schema, timeoutMs := 10000 }
    match ← ask liveRunner [backend] backend question dir with
    | .error failure => throw (IO.userError failure.describe)
    | .ok outcome =>
      ensure ((outcome.answer.getObjValAs? String "prompt").toOption == some prompt) "prompt changed in transport"
      ensure ((outcome.answer.getObjValAs? String "model").toOption == some "local/model") "configured model lost"
      ensure ((outcome.answer.getObjValAs? String "mode").toOption == some "question") "wrong adapter mode"
    let invalid : Question := { question with schema := Lean.Json.mkObj [("type", "string")] }
    let rejected ← ask liveRunner [backend] backend invalid dir
    ensure rejected.toOption.isNone "schema-breaking process output accepted"
  for (executable, arguments) in [("printf", ["not json"]), ("false", [])] do
    let broken := { backend with harness := .command executable arguments }
    ensure (← ask liveRunner [broken] broken { prompt := "", schema, timeoutMs := 10000 } dir).toOption.isNone
      "failed adapter accepted"
  for adapter in ["codex", "claude-code", "command"] do
    let json := Lean.Json.mkObj [("adapter", Lean.toJson adapter), ("model", Lean.toJson "chosen"),
      ("dataGoesTo", Lean.toJson "chosen destination"), ("command", Lean.toJson "cat"),
      ("args", Lean.toJson ([] : List String))]
    let parsed ← IO.ofExcept (backendOfJson json)
    ensure (parsed.model == "chosen" && parsed.dataGoesTo == "chosen destination") "configuration changed"
    ensure ((backendOfJson (Lean.Json.mkObj [("adapter", Lean.toJson adapter)])).toOption.isNone)
      "incomplete configuration accepted"
  let config := dir / "backend.json"
  IO.FS.writeFile config "{\"adapter\":\"command\",\"command\":\"cat\",\"args\":[],\"model\":\"default\",\"dataGoesTo\":\"local\"}"
  let source := dir / "Select.lean"
  IO.FS.writeFile source "import SpecTools.BackendConfig\n#eval show IO Unit from do\n  let b ← SpecTools.Model.selectedBackend \"configured\" \"override\"\n  if b.model != \"override\" then throw (IO.userError \"model override lost\")\n  match b.harness with\n  | .command \"cat\" [] => pure ()\n  | _ => throw (IO.userError \"configured adapter lost\")\n"
  let selected ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", source.toString]
    env := #[("SPEC_TOOLS_BACKEND", some config.toString)] }
  ensure (selected.exitCode == 0) s!"configured selection: {selected.stdout}{selected.stderr}"
  for model in ["", "  "] do
    let refused ← (selectedBackend "configured" model).toBaseIO
    ensure (match refused with | .error _ => true | .ok _ => false)
      "empty configured model override accepted"
  IO.FS.removeDirAll dir
  IO.println "PASS: configurable command adapter (transport, schema, malformed output, exit, configuration)"

def main : IO Unit := do
  testCommandAdapter
  let requirements ← IO.asTask testRequirementAudits
  testFinishedProcess
  testOverrun
  testAudit
  IO.ofExcept requirements.get
  IO.println "PASS: audit (pass, unchanged, changed, missing, unclaimed, axiom, vacuous)"
  liveCallsForbidden.set true
  let blocked ← (liveRunner { cmd := "true", args := #[], cwd := "." } [] 1000).toBaseIO
  ensure (match blocked with | .error _ => true | .ok _ => false)
    "a live call while forbidden is refused"
  IO.println "PASS: live runner (exit, output, files, overrun, forbidden)"
