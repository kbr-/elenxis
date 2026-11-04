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
  IO.FS.writeFile file ("import SpecTools.Audit\nopen SpecTools.Ledger\n" ++ body)
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

def main : IO Unit := do
  testFinishedProcess
  testOverrun
  testAudit
  IO.println "PASS: audit (pass, unchanged, changed, missing, unclaimed, axiom, vacuous)"
  liveCallsForbidden.set true
  let blocked ← (liveRunner { cmd := "true", args := #[], cwd := "." } [] 1000).toBaseIO
  ensure (match blocked with | .error _ => true | .ok _ => false)
    "a live call while forbidden is refused"
  IO.println "PASS: live runner (exit, output, files, overrun, forbidden)"
