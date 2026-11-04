import SpecTools.Ledger

/-!
`tests`: a ledger's rows against a target's Python property tests, through the adapter
`adapters/python_guards.py`. Two findings: a test a row names that the test file doesn't define
(coverage), and a guard of the implementation whose removal no test notices (a weak test). The
reading of the adapter's output and the findings are pure.
-/

namespace SpecTools.Tests
open Lean SpecTools.Ledger

/-- One guard's result: its line, its text, and the tests that failed with it removed. -/
structure GuardResult where
  line : Nat
  guard : String
  failed : List String
  deriving Repr, DecidableEq, Inhabited

inductive Finding where
  /-- A row names a test the test file doesn't define. -/
  | missingTest (row test : String)
  /-- No test fails when this guard is removed. -/
  | weakTest (line : Nat) (guard : String)
  deriving Repr, DecidableEq, Inhabited

def Finding.describe : Finding → String
  | .missingTest r t => s!"coverage: row {r} names {t}, which the test file doesn't define"
  | .weakTest l g => s!"weak test: no test fails with the guard `{g}` (line {l}) removed"

def findings (rows : List Row) (defined : List String) (guards : List GuardResult) : List Finding :=
  (rows.flatMap fun r => (r.tests.filter (!defined.contains ·)).map (.missingTest r.id)) ++
    (guards.filter (·.failed.isEmpty)).map fun g => .weakTest g.line g.guard

/-- The adapter's output: the tests defined, then each guard. -/
def parse (lines : List String) : Except String (List String × List GuardResult) := do
  match lines with
  | [] => throw "the adapter printed nothing"
  | first :: rest =>
    let defined ← (Json.parse first >>= (·.getObjValAs? (List String) "tests"))
    let guards ← rest.filter (· ≠ "") |>.mapM fun l => do
      let j ← Json.parse l
      return { line := ← j.getObjValAs? Nat "line", guard := ← j.getObjValAs? String "guard",
               failed := ← j.getObjValAs? (List String) "failed" }
    return (defined, guards)

/-- Run the adapter on `module` and `testFile` for every test the rows name, and print the
findings; fails when there is one. -/
def run (rows : List Row) (adapter module testFile : String) (cwd : Option String := none) :
    IO Unit := do
  let tests := (rows.flatMap (·.tests)).eraseDups
  let out ← IO.Process.output
    { cmd := "python3", args := #[adapter, module, testFile] ++ tests.toArray, cwd := cwd }
  if out.exitCode != 0 then throw <| IO.userError s!"the adapter failed:\n{out.stderr}"
  let (defined, guards) ← IO.ofExcept (parse (out.stdout.splitOn "\n"))
  let fs := findings rows defined guards
  for f in fs do IO.println f.describe
  IO.println s!"{guards.length} guards, {tests.length} tests named, {fs.length} findings"
  unless fs.isEmpty do throw <| IO.userError "tests: findings above"

end SpecTools.Tests
