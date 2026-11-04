import SpecTools.Audit
import SpecTools.Gaps

/-!
Running `gaps` from a project's ledger file: `#eval SpecTools.Gaps.run rows prose backend` gathers
the facts as the audit does, asks the model for the gaps Lean can't decide, and prints the report.
-/

namespace SpecTools.Gaps
open Lean Elab Command SpecTools.Ledger SpecTools.Model SpecTools.Audit

def gapsPrompt (prose : String) (rows : List Row) (facts : Facts) : String :=
  let rowText := rows.map fun r =>
    let stmts := r.theorems.filterMap fun n => (facts n).map fun f => s!"    {n} : {f.statement}"
    s!"- {r.id}: {r.clause}\n" ++ "\n".intercalate stmts
  "Below are requirements in prose and a ledger of rows, each row a clause with the Lean \
  statements claimed to establish it. Report each gap: `uncovered` (a clause of the prose no row \
  states, or a row whose statements don't establish its clause), `too weak` (a statement weaker \
  than its clause), `undecided` (a case the prose leaves open that the statements decide), \
  `extra` (a statement the prose doesn't ask for). Name the row each gap concerns by its \
  identifier; for a clause no row has, name the row nearest it. Report nothing when there is no \
  gap.\n\n# Prose\n\n" ++ prose ++ "\n\n# Ledger\n\n" ++ "\n".intercalate rowText

/-- Print the gaps of the ledger `rows` against `prose`, asking `backend` for what Lean can't decide. -/
def run (rows : List Row) (prose : String) (backend : Backend) (timeoutMs : Nat := 300000) :
    CommandElabM Unit := do
  let names := (rows.flatMap fun r => r.theorems ++ r.witnesses).eraseDups
  let mut table : List (Name × Fact) := []
  for n in names do
    if let some f ← factOf n then table := (n, f) :: table
  let facts : Facts := fun n => table.lookup n
  let scratch ← IO.FS.createTempDir
  let answer ← ask liveRunner [backend] backend
    { prompt := gapsPrompt prose rows facts, schema := proposalSchema, timeoutMs } scratch
  IO.FS.removeDirAll scratch
  let proposals ← match answer with
    | .ok o => match proposalsOf o.answer with
      | some ps => pure ps
      | none => throwError "the model's answer is no list of gaps"
    | .error f => throwError f.describe
  let report := gather facts rows proposals
  let mut total := 0
  for k in kinds do
    for g in report.byKind k do
      total := total + 1
      IO.println s!"{k.name}: {g.row}: {g.why}"
  for e in report.refused do IO.println s!"refused as malformed: {e}"
  IO.println s!"{total} gaps, {report.refused.length} proposals refused"

end SpecTools.Gaps
