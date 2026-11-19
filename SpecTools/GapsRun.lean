import SpecTools.Audit
import SpecTools.Gaps
import SpecTools.BackendConfig

/-!
Running `gaps` from a project's ledger file: `#eval SpecTools.Gaps.run rows prose backend` gathers
the facts as the audit does, asks the model for the gaps Lean can't decide, and prints the report.
-/

namespace SpecTools.Gaps
open Lean Elab Command SpecTools.Ledger SpecTools.Model SpecTools.Audit

def gapsPrompt (prose : String) (rows : List Row) (facts : Facts) : String :=
  -- A row's witnesses are listed apart from its statements: a witness shows a statement's
  -- hypotheses can hold, and judged as a statement of the clause it reads as an extra one.
  let rowText := rows.map fun r =>
    let line (n : Name) : Option String := (facts n).map fun f =>
      s!"    {n} [{reprStr f.kind}] : {f.statement}"
    let stmts := r.theorems.eraseDups.filterMap line
    let witnesses := (r.witnesses.eraseDups.filter (!r.theorems.contains ·)).filterMap line
    s!"- {r.id}: {r.clause}\n" ++ "\n".intercalate stmts ++
      (if witnesses.isEmpty then "" else
        "\n  witnesses (not statements of the clause):\n" ++ "\n".intercalate witnesses)
  "A requirement declaration states an unproved obligation; it does not establish its truth. \
  For those declarations, judge whether the proposition states the required behavior completely. \
  Below are requirements in prose and a ledger of rows, each row a clause with the Lean \
  statements claimed to establish it, and under `witnesses` the facts showing those statements' \
  hypotheses can hold; a witness is not a statement of the clause, so judge none as a gap. \
  Report each gap: `uncovered` (a clause of the prose no row \
  states, or a row whose statements don't establish its clause), `too weak` (a statement weaker \
  than its clause), `undecided` (a case the prose leaves open that the statements decide), \
  `extra` (a statement of behaviour the prose neither asks for nor implies; a statement giving a \
  clause another form, such as an invariant after a step for a limit at the step, is not extra). \
  Name the row each gap concerns by its \
  identifier; for a clause no row has, name the row nearest it. Report nothing when there is no \
  gap.\n\n# Prose\n\n" ++ prose ++ "\n\n# Ledger\n\n" ++ "\n".intercalate rowText

/-- Print the gaps of the ledger `rows` against `prose`, asking `backend` for what Lean can't decide. -/
def run (rows : List Row) (prose : String) (backend : Backend) (timeoutMs : Nat := 300000)
    (requirements : Bool := false) :
    CommandElabM Unit := do
  let names := (rows.flatMap fun r => r.theorems ++ r.witnesses).eraseDups
  let mut table : List (Name × Fact) := []
  for n in names do
    if let some f ← factOf n requirements then table := (n, f) :: table
  let facts : Facts := fun n => table.lookup n
  IO.ofExcept (validateRequirements requirements facts rows)
  IO.println s!"Requirements check: {backend.describe}"
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

/-- The same checker with its backend selected by deployment configuration. -/
def runConfigured (rows : List Row) (prose : String) (timeoutMs : Nat := 300000)
    (requirements : Bool := false) : CommandElabM Unit := do
  run rows prose (← configuredBackend) timeoutMs requirements

structure DraftSource where
  id : String
  clause : String
  deriving BEq, FromJson

inductive DraftEvidence where
  | contract (name : Name) (statement : String)
  | externalCheck (reason acceptance : String)
  deriving FromJson

structure DraftRow where
  source : DraftSource
  evidence : DraftEvidence
  deriving FromJson

def draftIssues (inventory : List DraftSource) (draft : List DraftRow) : List String :=
  let expected : List Row := inventory.map fun item => { id := item.id, clause := item.clause }
  let actual : List Row := draft.map fun row => { id := row.source.id, clause := row.source.clause }
  (if inventory.isEmpty then ["Requirement inventory is empty."] else []) ++
  ((repeatedIds expected).map fun id => s!"Duplicate requirement key: {id}") ++
  ((repeatedIds actual).map fun id => s!"Duplicate draft key: {id}") ++
  (inventory.filterMap fun item =>
    if draft.any (fun row => row.source.id == item.id) then none
    else some s!"Missing draft row: {item.id}") ++
  (draft.flatMap fun row =>
    (if inventory.any (· == row.source) then []
     else [s!"Unknown or changed source clause: {row.source.id}"]) ++
    match row.evidence with
    | .contract name statement =>
      if name.isAnonymous || statement.trimAscii.isEmpty then
        [s!"Empty draft contract: {row.source.id}"] else []
    | .externalCheck reason acceptance =>
      if reason.trimAscii.isEmpty || acceptance.trimAscii.isEmpty then
        [s!"External check needs a reason and acceptance case: {row.source.id}"] else [])

def draftPrompt (prose : String) (draft : List DraftRow) : String :=
  let contracts := (draft.filterMap fun row => match row.evidence with
    | .contract name statement => some (name, statement)
    | .externalCheck .. => none).eraseDups.zipIdx
  let rows := draft.map fun row =>
    let evidence := match row.evidence with
      | .contract name statement =>
        s!"Draft Lean contract {name}, statement {(contracts.lookup (name, statement)).getD 0}"
      | .externalCheck reason acceptance => s!"External evidence ({reason}): {acceptance}"
    s!"- {row.source.id}: {row.source.clause}\n  {evidence}"
  "Review the complete Coverage draft against the requirements. " ++
  "Compare draft contract statements and external acceptance cases with the requirements. " ++
  "Report missing, weaker, undecided or extra behavior as uncovered, too weak, undecided or extra. " ++
  "Cite one draft row ID per proposal. Put other related IDs in the reason. " ++
  "An empty gaps array means you found no gaps.\n\n# Prose\n" ++
    prose ++ "\n\n# Coverage draft\n" ++ "\n".intercalate rows ++ "\n\n# Contract statements\n" ++
    "\n".intercalate (contracts.map fun ((name, statement), index) =>
      s!"- Statement {index}, {name}: {statement}")

def reviewDraft (runner : Runner) (allowed : List Backend) (backend : Backend)
    (inventory : List DraftSource) (draft : List DraftRow) (prose : String)
    (scratch : System.FilePath) (timeoutMs : Nat := 300000) : IO (Except String Report) := do
  let issues := draftIssues inventory draft
  unless issues.isEmpty do
    return .error ("Submit the full Coverage draft together.\n" ++ "\n".intercalate issues)
  match ← ask runner allowed backend
      { prompt := draftPrompt prose draft,
        schema := proposalSchemaFor (some (inventory.map (·.id))), timeoutMs } scratch with
  | .error failure => return .error failure.describe
  | .ok outcome =>
    let some proposals := proposalsOf outcome.answer
      | return .error "The review answer is no list of gaps."
    let rows := draft.map fun row => ({ id := row.source.id, clause := row.source.clause } : Row)
    return .ok (gather (fun _ => none) rows proposals)

def draftContractNames (draft : List DraftRow) : List Name :=
  (draft.filterMap fun row => match row.evidence with
    | .contract name _ => some name
    | .externalCheck .. => none).eraseDups

def contractBindingIssues (draft : List DraftRow) (bindings : List ApprovedContract) : List String :=
  let expected := draftContractNames draft
  let actual := bindings.map (·.declaration)
  let distinct := actual.eraseDups
  (expected.filterMap fun name =>
    if actual.contains name then none else some s!"Missing final contract binding: {name}") ++
  (distinct.filterMap fun name =>
    if expected.contains name then none else some s!"Unreviewed final contract binding: {name}") ++
  (distinct.filterMap fun name =>
    if actual.count name > 1 then some s!"Duplicate final contract binding: {name}" else none)

def checkDraftContracts (draft : List DraftRow) (bindings : List ApprovedContract) :
    CommandElabM Unit := do
  let issues := contractBindingIssues draft bindings
  unless issues.isEmpty do
    throwError "Specification contract bindings differ from Coverage:\n{String.intercalate "\n" issues}"
  checkApprovedContracts bindings

end SpecTools.Gaps
