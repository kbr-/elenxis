import SpecTools.Ledger

/-!
The audit: the ledger's rows judged against the Lean environment they're run in. This layer gathers
the facts (each named theorem's statement, axioms and hypotheses; the theorems written under the
project's module root; the modules the audit doesn't import) and prints the pure core's verdicts.
-/

namespace SpecTools.Audit
open Lean Elab Command Meta SpecTools.Ledger

private def underRoot (env : Environment) (root : Name) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == root
  | none => true

/-- Theorems written in a source file under `root`, without the ones Lean generates. -/
def writtenTheorems (env : Environment) (root : Name) : CommandElabM (List Name) := do
  let candidates := env.constants.fold (init := []) fun found name info =>
    if info matches .thmInfo _ && !name.isInternal && underRoot env root name &&
        !env.isProjectionFn name then name :: found
    else found
  candidates.filterM fun name => return (← findDeclarationRanges? name).isSome

/-- The source modules under `dir` that the environment doesn't hold. -/
def missingModules (env : Environment) (dir : System.FilePath) : CommandElabM (List String) := do
  let files ← dir.walkDir
  let names := files.toList.filterMap fun file =>
    if file.extension == some "lean" then
      some <| (file.withExtension "").components.foldl (fun name part => name.str part) .anonymous
    else none
  return (names.filter (!env.header.moduleNames.contains ·)).map toString

/-- What the environment says of a name. -/
def factOf (name : Name) : CommandElabM (Option Fact) := do
  match (← getEnv).find? name with
  | some (.thmInfo info) =>
    let statement := toString (← liftTermElabM <| ppExpr info.type)
    let axioms := (← liftCoreM <| collectAxioms name).toList
    let hypotheses ← liftTermElabM <| forallTelescope info.type fun xs _ =>
      xs.anyM fun x => do isProp (← inferType x)
    return some { statement, axioms, hypotheses }
  | _ => return none

/-- Read stored digests: one `id digest` per line; a missing file is no digests. -/
def readDigests (path : System.FilePath) : IO (List (String × UInt64)) := do
  unless ← path.pathExists do return []
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun line =>
    match line.splitOn " " with
    | [id, d] => d.toNat?.map fun n => (id, n.toUInt64)
    | _ => none

def writeDigests (path : System.FilePath) (ds : List (String × UInt64)) : IO Unit :=
  IO.FS.writeFile path (String.join (ds.map fun (id, d) => s!"{id} {d}\n"))

/-- Judge the ledger's rows and print each verdict with the statements and axioms behind it. Fails
on what makes the report wrong: a repeated identifier, a named theorem that is no theorem, a written
theorem no row claims, a source module the audit doesn't import. A row not stated, conditional or
too weak fails nothing: the report exists to show it. With `digestFile`, rows whose clause and named
statements are unchanged since the last run are listed as unchanged and not re-judged. -/
def run (rows : List Row) (root : Name) (sourceDir : Option System.FilePath := none)
    (digestFile : Option System.FilePath := none) : CommandElabM Unit := do
  let env ← getEnv
  let names := (rows.flatMap fun r => r.theorems ++ r.witnesses).eraseDups
  let mut table : List (Name × Fact) := []
  for n in names do
    if let some f ← factOf n then table := (n, f) :: table
  let facts : Facts := fun n => table.lookup n
  let stored ← match digestFile with
    | some p => readDigests p
    | none => pure []
  let judged := toRejudge stored facts rows
  let mut errors : List String := (repeatedIds rows).map (s!"row {·} is listed twice")
  let mut counts : List (String × Nat) := []
  for row in rows do
    if !judged.any (·.id == row.id) then
      IO.println s!"unchanged: {row.id}"
      continue
    let v := verdict facts row
    if let .missing n := v then errors := errors ++ [s!"{row.id} names {n}, which is no theorem"]
    counts := match counts.lookup v.label with
      | some k => (v.label, k + 1) :: counts.filter (·.1 != v.label)
      | none => (v.label, 1) :: counts
    IO.println s!"{v.label}: {row.id}: {row.clause}"
    for n in row.theorems ++ row.witnesses do
      if let some f := facts n then
        IO.println s!"  {n} : {f.statement}"
        IO.println s!"    axioms: {f.axioms}{if f.hypotheses then ", has hypotheses" else ""}"
  for n in unclaimed rows (← writtenTheorems env root) do
    errors := errors ++ [s!"no row claims theorem {n}"]
  if let some dir := sourceDir then
    for m in ← missingModules env dir do
      errors := errors ++ [s!"the audit does not import module {m}"]
  IO.println s!"{rows.length} rows, {judged.length} judged: {counts.reverse}"
  if let some p := digestFile then
    if errors.isEmpty then writeDigests p (digests facts rows)
  unless errors.isEmpty do
    throwError "audit failed:\n{"\n".intercalate errors}"

end SpecTools.Audit
