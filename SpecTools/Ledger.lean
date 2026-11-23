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

inductive EvidenceKind where
  | inhabited
  | inconsistent
  deriving Repr, DecidableEq, Inhabited

def EvidenceKind.label : EvidenceKind → String
  | .inhabited => "inhabitation"
  | .inconsistent => "contradiction"

/-- A proposed proof about the premise domain of a particular theorem. -/
structure EvidenceBinding where
  subject : Name
  proofName : Name
  kind : EvidenceKind := .inhabited
  deriving Repr, DecidableEq, Inhabited

/-- One clause of the prose and what covers it. -/
structure Row where
  id : String
  /-- The clause, quoted from the prose. -/
  clause : String
  /-- Where the clause stands: a file and line. -/
  source : String := ""
  /-- Theorems establishing the clause. -/
  theorems : List Name := []
  /-- Legacy witness names, retained for declaration coverage. -/
  witnesses : List Name := []
  /-- Tests covering the clause in other languages, by name. -/
  tests : List String := []
  status : Status := .covered
  /-- Claims about individual theorem premise domains, checked by the audit. -/
  evidence : List EvidenceBinding := []
  deriving Repr, Inhabited

abbrev CheckedEvidence := EvidenceBinding → Bool

def hasEvidence (checked : CheckedEvidence) (bindings : List EvidenceBinding)
    (subject : Name) (kind : EvidenceKind) : Bool :=
  bindings.any fun binding =>
    decide (binding.subject = subject) && decide (binding.kind = kind) && checked binding

inductive StatementKind where
  | theoremStatement
  | requirement
  | notProposition
  | unavailableBody
  deriving Repr, DecidableEq, Inhabited

def requirementKind (proposition bodyAvailable unsafeBody : Bool) : StatementKind :=
  if !proposition then .notProposition
  else if bodyAvailable && !unsafeBody then .requirement else .unavailableBody

/-- A checked declaration's statement and proof status. -/
structure Fact where
  statement : String
  axioms : List Name
  /-- The statement has a hypothesis (a binder whose type is a proposition). -/
  hypotheses : Bool
  kind : StatementKind := .theoremStatement
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
  /-- A theorem has premises without a checked certificate of inhabitation. -/
  | tooWeakOrVacuous
  | inconsistentPremises
  | proved
  | specified
  | notProposition (name : Name)
  | unavailableBody (name : Name)
  deriving Repr, BEq, Inhabited

def Verdict.label : Verdict → String
  | .missing n => s!"names {n}, which is no theorem"
  | .notStated => "not stated"
  | .conditional _ => "conditional"
  | .tooWeakOrVacuous => "unknown nonvacuity"
  | .inconsistentPremises => "inconsistent premises"
  | .proved => "proved"
  | .specified => "specified (unproved)"
  | .notProposition n => s!"{n} is not a proposition"
  | .unavailableBody n => s!"{n} has no inspectable requirement body"

/-- The first name of `names` that is no theorem. -/
def firstMissing (facts : Facts) : List Name → Option Name
  | [] => none
  | n :: ns => if (facts n).isNone then some n else firstMissing facts ns

def Fact.unacceptedAxioms (fact : Fact) : List Name :=
  fact.axioms.filter (!acceptedAxioms.contains ·)

/-- The axioms outside the accepted three that the given theorems rest on. -/
def unaccepted (facts : Facts) (names : List Name) : List Name :=
  (names.flatMap fun n => match facts n with
    | some f => f.unacceptedAxioms
    | none => []).eraseDups

def premiseVerdict (facts : Facts) (row : Row) (checked : CheckedEvidence) : Verdict :=
  let guarded := row.theorems.filter fun name => (facts name).any (·.hypotheses)
  if guarded.any (hasEvidence checked row.evidence · .inconsistent) then .inconsistentPremises
  else if guarded.all (hasEvidence checked row.evidence · .inhabited) then .proved
  else .tooWeakOrVacuous

/-- The row's verdict. A binding is evidence only after checking in the Lean environment. -/
def verdict (facts : Facts) (row : Row) (checked : CheckedEvidence := fun _ => false) : Verdict :=
  match firstMissing facts (row.theorems ++ row.witnesses) with
  | some n => .missing n
  | none =>
    if let some n := (row.theorems ++ row.witnesses).find?
        (fun n => (facts n).any (·.kind == .notProposition)) then .notProposition n
    else if let some n := (row.theorems ++ row.witnesses).find?
        (fun n => (facts n).any (·.kind == .unavailableBody)) then .unavailableBody n
    else if row.theorems.isEmpty then .notStated
    else match unaccepted facts (row.theorems ++ row.witnesses) with
      | a :: as => .conditional (a :: as)
      | [] =>
        if (row.theorems ++ row.witnesses).all
            (fun n => (facts n).any (·.kind == .theoremStatement)) then
          premiseVerdict facts row checked
        else .specified

inductive SpecificationFinding where
  | emptyLedger
  | unstated (clause : String)
  | missing (clause : String) (name : Name)
  | notProposition (clause : String) (name : Name)
  | unavailableBody (clause : String) (name : Name)
  | untrusted (clause : String) (name : Name) (axioms : List Name)
  | missingWitness (clause : String)
  | inconsistentPremises (clause : String)
  | unprovedWitness (clause : String) (name : Name)
  | duplicate (clause : String)
  deriving Repr, DecidableEq

def SpecificationFinding.render : SpecificationFinding → String
  | .emptyLedger => "the specification ledger is empty"
  | .unstated id => s!"{id}: not stated"
  | .missing id name => s!"{id}: names {name}, which is no admitted statement"
  | .notProposition id name => s!"{id}: {name} is not a proposition"
  | .unavailableBody id name => s!"{id}: {name} has no inspectable safe requirement body"
  | .untrusted id name axioms => s!"{id}: {name} is conditional on {axioms}"
  | .missingWitness id => s!"{id}: unknown nonvacuity"
  | .inconsistentPremises id => s!"{id}: inconsistent premises"
  | .unprovedWitness id name => s!"{id}: witness {name} is not proved"
  | .duplicate id => s!"{id}: repeated clause identifier"

def declarationFinding (facts : Facts) (id : String) (name : Name) : Option SpecificationFinding :=
  match facts name with
  | none => some (.missing id name)
  | some fact =>
    match fact.kind with
    | .notProposition => some (.notProposition id name)
    | .unavailableBody => some (.unavailableBody id name)
    | .theoremStatement | .requirement =>
      match fact.unacceptedAxioms with
      | [] => none
      | axioms => some (.untrusted id name axioms)

/-- Identifiers given to more than one row. -/
def repeatedIds (rows : List Row) : List String :=
  let ids := rows.map (·.id)
  ids.eraseDups.filter fun id => ids.count id > 1

def witnessFinding (facts : Facts) (id : String) (name : Name) : Option SpecificationFinding :=
  if (facts name).any (·.kind == .requirement) then some (.unprovedWitness id name) else none

def specificationFindings (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence := fun _ => false) : List SpecificationFinding :=
  (if rows.isEmpty then [.emptyLedger] else []) ++
    (repeatedIds rows).map SpecificationFinding.duplicate ++
    rows.flatMap fun row =>
      (if row.theorems.isEmpty then [.unstated row.id] else []) ++
        (row.theorems ++ row.witnesses).eraseDups.filterMap (declarationFinding facts row.id) ++
        row.witnesses.eraseDups.filterMap (witnessFinding facts row.id) ++
        (match verdict facts row checked with
          | .tooWeakOrVacuous => [.missingWitness row.id]
          | .inconsistentPremises => [.inconsistentPremises row.id]
          | _ => [])

def specificationIssues (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence := fun _ => false) : List String :=
  (specificationFindings facts rows checked).map SpecificationFinding.render

def auditIssues (requirements : Bool) (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence := fun _ => false) : List String :=
  if requirements then specificationIssues facts rows checked else []

def validateRequirements (requirements : Bool) (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence := fun _ => false) : Except String Unit :=
  match auditIssues requirements facts rows checked with
  | [] => .ok ()
  | issues => .error (String.intercalate "\n" issues)

def specificationSuffix (requirements : Bool) (specified : Nat) : String :=
  if requirements then s!", {specified} specified (unproved)" else ""

/-- The written theorems no row claims. -/
def unclaimed (rows : List Row) (written : List Name) : List Name :=
  let claimed := rows.flatMap fun r => r.theorems ++ r.witnesses ++ r.evidence.map (·.proofName)
  written.filter (!claimed.contains ·)

/-! Following changes: a row is re-judged only when its clause or a statement it names changed. -/

/-- What a row's verdict depends on: its clause and the statements and axioms it names. -/
def digestInput (facts : Facts) (row : Row) (checked : CheckedEvidence := fun _ => false) : String :=
  let named := (row.theorems ++ row.witnesses ++ row.evidence.map (·.proofName)).map fun n => match facts n with
    | some f => s!"{n} : {f.statement} / {f.axioms} / {f.hypotheses} / {reprStr f.kind}"
    | none => s!"{n} missing"
  let evidence := row.evidence.map fun binding => s!"{repr binding}: {checked binding}"
  String.intercalate "\n" (row.clause :: named ++ evidence)

def digest (facts : Facts) (row : Row) (checked : CheckedEvidence := fun _ => false) : UInt64 :=
  hash (digestInput facts row checked)

/-- The rows whose digest differs from the one stored for their identifier. -/
def toRejudge (stored : List (String × UInt64)) (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence := fun _ => false) : List Row :=
  rows.filter fun r => stored.lookup r.id != some (digest facts r checked)

/-- The digests to store after a run. -/
def digests (facts : Facts) (rows : List Row) (checked : CheckedEvidence := fun _ => false) :
    List (String × UInt64) :=
  rows.map fun r => (r.id, digest facts r checked)

end SpecTools.Ledger
