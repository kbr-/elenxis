-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Adversarial

namespace SpecTools.RelationAudit
open Lean Meta Elab Command

variable {X : Type u} {Y : X → Type v}

def inhabited (a : X → Prop) (r : (x : X) → Y x → Prop) :=
  ∃ x, a x ∧ ∃ y, r x y

def total (a : X → Prop) (r : (x : X) → Y x → Prop) :=
  ∀ x, a x → ∃ y, r x y

def uniqueOutputs (a : X → Prop) (r : (x : X) → Y x → Prop) :=
  ∀ x, a x → ∀ y z, r x y → r x z → y = z

def missingAt (a : X → Prop) (r : (x : X) → Y x → Prop) (x : X) :=
  a x ∧ ¬ ∃ y, r x y

def admitsAt (a : X → Prop) (r : (x : X) → Y x → Prop) (x : X) (y : Y x) :=
  a x ∧ r x y

def together (r s : (x : X) → Y x → Prop) (x : X) (y : Y x) := r x y ∧ s x y

theorem missing_refutes_total {a : X → Prop} {r : (x : X) → Y x → Prop} {x}
    (h : missingAt a r x) : ¬ total a r := fun t => h.2 (t x h.1)

theorem joint_total_left {a : X → Prop} {r s : (x : X) → Y x → Prop}
    (h : total a (together r s)) : total a r := by
  intro x hx
  obtain ⟨y, hr, _⟩ := h x hx
  exact ⟨y, hr⟩

inductive Scope where
  | inhabited | total | uniqueOutputs | missingAt (input : Name)
  | admitsAt (input output : Name)
  deriving ToJson

structure Claim where
  admissible : Name
  members : List (String × Name)
  scope : Scope
  supports : List Name := []
  refutes : List Name := []
  deriving ToJson

private def rigid (name : Name) : MetaM Expr := do
  discard <| Adversarial.safeTermMeta name
  let info ← getConstInfo name
  return mkConst name (info.levelParams.map Level.param)

private def proposition (claim : Claim) : MetaM Expr := do
  let first :: rest := claim.members.map Prod.snd | throwError "Expected at least one requirement"
  let mut relation ← rigid first
  for name in rest do
    relation ← mkAppM ``together #[relation, ← rigid name]
  let a ← rigid claim.admissible
  let p ← match claim.scope with
    | .inhabited => mkAppM ``inhabited #[a, relation]
    | .total => mkAppM ``total #[a, relation]
    | .uniqueOutputs => mkAppM ``uniqueOutputs #[a, relation]
    | .missingAt input => mkAppM ``missingAt #[a, relation, ← rigid input]
    | .admitsAt input output => mkAppM ``admitsAt #[a, relation, ← rigid input, ← rigid output]
  let p ← instantiateMVars p
  if p.hasMVar then throwError "Ambiguous relation scope"
  return p

def association (rows : Option (List Evidence.Requirement)) (id : String) (decl : Name) : String :=
  match rows with
  | none => "author-supplied"
  | some ledger => match ledger.filter (·.id == id) with
    | [] => "missing"
    | [row] => if row.declarations.contains decl then "validated" else "mismatched"
    | _ => "ambiguous"

/-- Audit a conjunction over the same input and output using named theorem evidence. -/
def review (claim : Claim) (requirementsFile : Option System.FilePath := none)
    (ledger : Option (List Ledger.Row) := none) (expected : Option Bool := none) : CommandElabM Json := do
  let ids := claim.members.map Prod.fst
  if ids.any (·.trimAscii.isEmpty) || ids.eraseDups != ids then throwError "Expected distinct requirement IDs"
  let p ← liftTermElabM <| proposition claim
  let mut certificates := #[]
  let mut supports := false
  let mut refutes := false
  for (names, negative) in [(claim.supports, false), (claim.refutes, true)] do
    for name in names do
      let (accepted, axioms) ← Audit.inspectCertificate name (if negative then mkApp (mkConst ``Not) p else p)
      if negative then refutes := refutes || accepted else supports := supports || accepted
      certificates := certificates.push <| Json.mkObj [("name", toJson name), ("negative", toJson negative),
        ("accepted", toJson accepted), ("axioms", toJson axioms)]
  let status := match Ledger.domainResult supports refutes with
    | .established => "established" | .refuted => "refuted"
    | .unresolved => "unresolved" | .conflicting => "conflicting"
  let roots := claim.admissible :: claim.members.map Prod.snd ++ claim.supports ++ claim.refutes ++
    (match claim.scope with | .missingAt n => [n] | .admitsAt x y => [x,y] | _ => [])
  let source ← Evidence.requirementSource requirementsFile
  let manifest : Option Evidence.Manifest ← Evidence.readManifest
  let supplied : Option (List Evidence.Requirement) := ledger.map (List.map fun row =>
    ({ id := row.id, clause := row.clause, declarations := row.theorems } : Evidence.Requirement))
  let links := claim.members.map fun (id, decl) =>
    let checked := association (supplied <|> manifest.map Evidence.Manifest.requirements) id decl
    let status := match supplied, manifest with
      | some localRows, some m =>
        if checked == "validated" && toJson (localRows.filter (fun (r : Evidence.Requirement) => r.id == id)) !=
            toJson (m.requirements.filter (fun (r : Evidence.Requirement) => r.id == id)) then "stale" else checked
      | _, _ => checked
    Json.mkObj [("id", toJson id), ("declaration", toJson decl), ("status", toJson status)]
  Evidence.attachWith manifest `SpecTools.RelationAudit.review "relation.v1"
    (toJson (claim, Ledger.acceptedAxioms, source, supplied, expected)) roots <|
    Json.mkObj [("schema", "elenxis.relation.v1"), ("requirements", toJson ids), ("claim", toJson claim),
    ("proposition", toJson (← liftTermElabM <| ppExpr p).pretty), ("certificates", .arr certificates),
    ("status", toJson status), ("associations", toJson links), ("expected", toJson expected)]

end SpecTools.RelationAudit
