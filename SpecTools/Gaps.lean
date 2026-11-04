import SpecTools.Ledger
import SpecTools.Model

/-!
`gaps`: the four gaps between the prose and the formal statements. Lean decides what it can: a row
whose theorems have hypotheses and no witness is too weak or vacuous with no model asked. A model
proposes the rest (a clause no statement covers, a statement weaker than its clause, a case the
prose leaves undecided, a statement the prose doesn't ask for); a proposal naming a row the ledger
lacks is refused as malformed. The core is pure; asking the model is a thin layer on `ask`.
-/

namespace SpecTools.Gaps
open Lean SpecTools.Ledger SpecTools.Model

inductive Kind where
  | uncovered | tooWeak | undecided | extra
  deriving Repr, DecidableEq, Inhabited

def Kind.name : Kind → String
  | .uncovered => "uncovered"
  | .tooWeak => "too weak"
  | .undecided => "undecided"
  | .extra => "extra"

def Kind.parse : String → Option Kind
  | "uncovered" => some .uncovered
  | "too weak" => some .tooWeak
  | "undecided" => some .undecided
  | "extra" => some .extra
  | _ => none

/-- A gap: its kind, the row it concerns, and why. -/
structure Gap where
  kind : Kind
  row : String
  why : String
  deriving Repr, DecidableEq, Inhabited

/-- A model's proposal as it came: its kind and row as written. -/
structure Proposal where
  kind : String
  row : String
  why : String
  deriving Repr, DecidableEq, Inhabited

/-- The gaps Lean decides: rows judged too weak or vacuous. -/
def decided (facts : Facts) (rows : List Row) : List Gap :=
  rows.filterMap fun r =>
    if verdict facts r == .tooWeakOrVacuous then
      some ⟨.tooWeak, r.id, "its theorems have hypotheses and no witness shows they can hold"⟩
    else none

/-- A proposal as a gap, or why it is malformed: an unknown kind, or a row the ledger lacks. The
refusal carries the proposal's kind and reason, so a person reads what was proposed. -/
def accept (rows : List Row) (p : Proposal) : Except String Gap :=
  match Kind.parse p.kind with
  | none => .error s!"unknown kind \"{p.kind}\" on row \"{p.row}\": {p.why}"
  | some k =>
    if rows.any (·.id == p.row) then .ok ⟨k, p.row, p.why⟩
    else .error s!"row \"{p.row}\" is not in the ledger: {p.kind}: {p.why}"

/-- What `gaps` prints: the gaps of each kind, and the proposals refused as malformed. -/
structure Report where
  byKind : Kind → List Gap
  refused : List String

/-- The order kinds are printed in. -/
def kinds : List Kind := [.uncovered, .tooWeak, .undecided, .extra]

def gather (facts : Facts) (rows : List Row) (proposals : List Proposal) : Report :=
  let accepted := proposals.filterMap fun p => (accept rows p).toOption
  let refused := proposals.filterMap fun p => match accept rows p with
    | .error e => some e
    | .ok _ => none
  let all := decided facts rows ++ accepted
  { byKind := fun k => all.filter (·.kind == k), refused }

def proposalSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("gaps", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "object"),
        ("properties", Json.mkObj [("kind", Json.mkObj [("type", "string"),
            ("enum", Json.arr #["uncovered", "too weak", "undecided", "extra"])]),
          ("row", Json.mkObj [("type", "string")]), ("why", Json.mkObj [("type", "string")])]),
        ("required", Json.arr #["kind", "row", "why"]), ("additionalProperties", false)])])]),
    ("required", Json.arr #["gaps"]), ("additionalProperties", false)]

def proposalsOf (answer : Json) : Option (List Proposal) := do
  let arr ← (answer.getObjValAs? (Array Json) "gaps").toOption
  arr.toList.mapM fun j => do
    let kind ← (j.getObjValAs? String "kind").toOption
    let row ← (j.getObjValAs? String "row").toOption
    let why ← (j.getObjValAs? String "why").toOption
    return { kind, row, why }

end SpecTools.Gaps
