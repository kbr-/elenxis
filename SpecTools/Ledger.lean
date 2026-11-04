import Lean

/-!
The requirements ledger's core: a row per clause of the prose, naming what covers it, and the
verdict the audit gives each row from facts about the theorems it names. The facts (`Facts`) are
gathered from a Lean environment by `SpecTools.Audit`; everything here is pure.
-/

namespace SpecTools.Ledger
open Lean

/-- A row's own account of its clause. -/
inductive Status where
  | covered
  | uncovered (reason : String)
  | provisional (decision : String)
  | accepted (decision : String)
  deriving Repr, BEq, Inhabited

/-- One clause of the prose and what covers it. -/
structure Row where
  id : String
  /-- The clause, quoted from the prose. -/
  clause : String
  /-- Where the clause stands: a file and line. -/
  source : String := ""
  /-- Theorems establishing the clause. -/
  theorems : List Name := []
  /-- Theorems exhibiting inputs that meet the clause's theorems' hypotheses. -/
  witnesses : List Name := []
  /-- Tests covering the clause in other languages, by name. -/
  tests : List String := []
  status : Status := .covered
  deriving Repr, Inhabited

/-- What the audit knows of a theorem. -/
structure Fact where
  statement : String
  axioms : List Name
  /-- The statement has a hypothesis (a binder whose type is a proposition). -/
  hypotheses : Bool
  deriving Repr, Inhabited

/-- The theorems of the project, by name; `none` for a name that is no theorem. -/
abbrev Facts := Name → Option Fact

def acceptedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

inductive Verdict where
  /-- A name the row gives is no theorem. -/
  | missing (name : Name)
  /-- The row names no theorem: the clause isn't stated in Lean. -/
  | notStated
  /-- A theorem rests on an axiom outside the accepted three. -/
  | conditional (axioms : List Name)
  /-- A theorem has hypotheses and the row gives no witness that they can hold. -/
  | tooWeakOrVacuous
  | proved
  deriving Repr, BEq, Inhabited

def Verdict.label : Verdict → String
  | .missing n => s!"names {n}, which is no theorem"
  | .notStated => "not stated"
  | .conditional axs => s!"conditional on {axs}"
  | .tooWeakOrVacuous => "too weak or vacuous"
  | .proved => "proved"

/-- The first name of `names` that is no theorem. -/
def firstMissing (facts : Facts) : List Name → Option Name
  | [] => none
  | n :: ns => if (facts n).isNone then some n else firstMissing facts ns

/-- The axioms outside the accepted three that the given theorems rest on. -/
def unaccepted (facts : Facts) (names : List Name) : List Name :=
  (names.flatMap fun n => match facts n with
    | some f => f.axioms.filter (!acceptedAxioms.contains ·)
    | none => []).eraseDups

/-- The row's verdict. -/
def verdict (facts : Facts) (row : Row) : Verdict :=
  match firstMissing facts (row.theorems ++ row.witnesses) with
  | some n => .missing n
  | none =>
    if row.theorems.isEmpty then .notStated
    else match unaccepted facts (row.theorems ++ row.witnesses) with
      | a :: as => .conditional (a :: as)
      | [] =>
        if row.witnesses.isEmpty && row.theorems.any (fun n => (facts n).any (·.hypotheses)) then
          .tooWeakOrVacuous
        else .proved

/-- The written theorems no row claims. -/
def unclaimed (rows : List Row) (written : List Name) : List Name :=
  let claimed := rows.flatMap fun r => r.theorems ++ r.witnesses
  written.filter (!claimed.contains ·)

/-- Identifiers given to more than one row. -/
def repeatedIds (rows : List Row) : List String :=
  let ids := rows.map (·.id)
  ids.eraseDups.filter fun id => ids.count id > 1

/-! Following changes: a row is re-judged only when its clause or a statement it names changed. -/

/-- What a row's verdict depends on: its clause and the statements and axioms it names. -/
def digestInput (facts : Facts) (row : Row) : String :=
  let named := (row.theorems ++ row.witnesses).map fun n => match facts n with
    | some f => s!"{n} : {f.statement} / {f.axioms}"
    | none => s!"{n} missing"
  String.intercalate "\n" (row.clause :: named)

def digest (facts : Facts) (row : Row) : UInt64 := hash (digestInput facts row)

/-- The rows whose digest differs from the one stored for their identifier. -/
def toRejudge (stored : List (String × UInt64)) (facts : Facts) (rows : List Row) : List Row :=
  rows.filter fun r => stored.lookup r.id != some (digest facts r)

/-- The digests to store after a run. -/
def digests (facts : Facts) (rows : List Row) : List (String × UInt64) :=
  rows.map fun r => (r.id, digest facts r)

end SpecTools.Ledger
