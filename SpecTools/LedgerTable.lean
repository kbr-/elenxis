import SpecTools.Ledger

/-!
The ledger's Markdown reader, for a clause table kept in a document: a table whose header row is
`| id | clause | source | theorems | witnesses | tests | status |`, a separator row, then one row per
clause. Names and tests are comma-separated; the status is `covered`, `uncovered: REASON`,
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

def rowOf (cells : List (List Char)) : Option Row :=
  match cells with
  | [id, clause, source, theorems, witnesses, tests, status] =>
    (statusOf status).map fun st =>
      { id := String.ofList id, clause := String.ofList clause, source := String.ofList source,
        theorems := (items theorems).map nameOf, witnesses := (items witnesses).map nameOf,
        tests := (items tests).map String.ofList, status := st }
  | _ => none

def isSeparator (cells : List (List Char)) : Bool :=
  cells.all fun c => !c.isEmpty && c.all (fun x => x == '-' || x == ':')

/-- The rows of the table in the lines given, numbered from `n`; the header and separator rows are
skipped, and a malformed row is refused with its line number. -/
def readLines : Nat → List (List Char) → Except String (List Row)
  | _, [] => .ok []
  | n, line :: rest =>
    match cellsOf line with
    | none => readLines (n + 1) rest
    | some cells =>
      if isSeparator cells || cells.head? == some "id".toList then readLines (n + 1) rest
      else match rowOf cells with
        | some row => (readLines (n + 1) rest).map (row :: ·)
        | none => .error s!"line {n}: not a ledger row (7 cells, the last a status)"

def readTable (text : String) : Except String (List Row) := readLines 1 (splitAt '\n' text.toList)

end SpecTools.Ledger
