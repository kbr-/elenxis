import SpecTools.LedgerTable

/-!
The Markdown reader: a table and the same rows written in Lean read equal; prose around the table
is ignored; a malformed row is refused with its line number.
-/

namespace SpecTools.Ledger
open Lean

deriving instance DecidableEq for Status
deriving instance DecidableEq for Row

def sampleTable : String :=
  "Prose before the table.\n\
  | id | clause | source | theorems | witnesses | tests | status |\n\
  |---|---|---|---|---|---|---|\n\
  | r1 | a loan ends by its due date | loans.md:3 | Loans.ends, Loans.due | Loans.someLoan | test_due | covered |\n\
  | r2 | a hold blocks renewal | loans.md:7 | | | | uncovered: not stated yet |\n\
  Prose after."

def sampleRows : List Row :=
  [{ id := "r1", clause := "a loan ends by its due date", source := "loans.md:3",
     theorems := [`Loans.ends, `Loans.due], witnesses := [`Loans.someLoan], tests := ["test_due"] },
   { id := "r2", clause := "a hold blocks renewal", source := "loans.md:7",
     status := .uncovered "not stated yet" }]

/-- The table and the same rows written in Lean are equal. -/
theorem table_reads_rows : (readTable sampleTable).toOption = some sampleRows := by decide +kernel

def refusal (r : Except String (List Row)) : Option String :=
  match r with
  | .error e => some e
  | .ok _ => none

/-- A row with a cell missing is refused, naming its line. -/
example : refusal (readTable "| id | clause | source | theorems | witnesses | tests | status |\n\
    |---|---|---|---|---|---|---|\n| r1 | c | s | t | w | covered |") =
    some "line 3: not a ledger row (7 cells, the last a status)" := by decide +kernel

/-- An unknown status is refused, naming its line. -/
example : refusal (readTable "| r1 | c | s | t | w | x | maybe |") =
    some "line 1: not a ledger row (7 cells, the last a status)" := by decide

/-- Every status form reads. -/
example : (["covered", "uncovered: r", "provisional: d", "accepted: d"].map fun s =>
    statusOf s.toList) = [some .covered, some (.uncovered "r"), some (.provisional "d"),
      some (.accepted "d")] := by decide

end SpecTools.Ledger
