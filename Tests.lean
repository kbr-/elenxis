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

def main : IO Unit := do
  testFinishedProcess
  testOverrun
  liveCallsForbidden.set true
  let blocked ← (liveRunner { cmd := "true", args := #[], cwd := "." } [] 1000).toBaseIO
  ensure (match blocked with | .error _ => true | .ok _ => false)
    "a live call while forbidden is refused"
  IO.println "PASS: live runner (exit, output, files, overrun, forbidden)"
