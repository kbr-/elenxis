import SpecTools.Ledger

/-!
The ledger's Markdown reader, for a clause table kept in a document: a table whose header row is
`| id | clause | source | theorems | witnesses | externalChecks | status |`, a separator row,
then one row per clause. The historical header `tests` selects the legacy field. Names are
comma-separated. Status is `covered`, `uncovered: REASON`,
`provisional: DECISION` or `accepted: DECISION`. Lines outside the table are prose and ignored.
Written over lists of characters with structural recursion, so the kernel evaluates it.
-/

namespace SpecTools.Ledger
open Lean

/-- `xs` split at each `c`. -/
def splitAt (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | x :: xs =>
    let rest := splitAt c xs
    if x = c then [] :: rest
    else match rest with
      | r :: rs => (x :: r) :: rs
      | [] => [[x]]

def trimChars (xs : List Char) : List Char :=
  ((xs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

def nameOf (xs : List Char) : Name :=
  (splitAt '.' xs).foldl (fun n part => n.str (String.ofList part)) .anonymous

/-- A cell's comma-separated items, empty ones dropped. -/
def items (cell : List Char) : List (List Char) :=
  ((splitAt ',' cell).map trimChars).filter (!·.isEmpty)

def startsWith (p xs : List Char) : Bool := xs.take p.length == p

def statusOf (cell : List Char) : Option Status :=
  let after (p : List Char) := String.ofList (trimChars (cell.drop p.length))
  if cell == "covered".toList then some .covered
  else if startsWith "uncovered:".toList cell then some (.uncovered (after "uncovered:".toList))
  else if startsWith "provisional:".toList cell then some (.provisional (after "provisional:".toList))
  else if startsWith "accepted:".toList cell then some (.accepted (after "accepted:".toList))
  else none

/-- A table line's cells, or none when the line isn't one (`| a | b |`). -/
def cellsOf (line : List Char) : Option (List (List Char)) :=
  let t := trimChars line
  match t with
  | '|' :: rest =>
    match rest.reverse with
    | '|' :: inner => some ((splitAt '|' inner.reverse).map trimChars)
    | _ => none
  | _ => none

def rowOf (cells : List (List Char)) (external : Bool := false) : Option Row :=
  match cells with
  | [id, clause, source, theorems, witnesses, checks, status] =>
    let names := (items checks).map String.ofList
    (statusOf status).map fun st =>
      { id := String.ofList id, clause := String.ofList clause, source := String.ofList source,
        theorems := (items theorems).map nameOf, witnesses := (items witnesses).map nameOf,
        tests := if external then [] else names, externalChecks := if external then names else [],
        status := st }
  | _ => none

theorem rowOf_check_names (id clause source theorems witnesses checks status : List Char)
    (external : Bool) :
    (rowOf [id, clause, source, theorems, witnesses, checks, status] external).map
        Row.externalCheckNames =
      (statusOf status).map (fun _ => ((items checks).map String.ofList).eraseDups) := by
  cases parsed : statusOf status <;> cases external <;>
    simp [rowOf, Row.externalCheckNames, parsed]

def isSeparator (cells : List (List Char)) : Bool :=
  cells.all fun c => !c.isEmpty && c.all (fun x => x == '-' || x == ':')

/-- The rows of the table in the lines given, numbered from `n`; the header and separator rows are
skipped, and a malformed row is refused with its line number. -/
def readLines : Nat → List (List Char) → (external : Bool := false) → Except String (List Row)
  | _, [], _ => .ok []
  | n, line :: rest, external =>
    match cellsOf line with
    | none => readLines (n + 1) rest external
    | some cells =>
      if cells.head? == some "id".toList then
        readLines (n + 1) rest (cells[5]? == some "externalChecks".toList)
      else if isSeparator cells then readLines (n + 1) rest external
      else match rowOf cells external with
        | some row => (readLines (n + 1) rest external).map (row :: ·)
        | none => .error s!"line {n}: not a ledger row (7 cells, the last a status)"

def readTable (text : String) : Except String (List Row) := readLines 1 (splitAt '\n' text.toList)

end SpecTools.Ledger
