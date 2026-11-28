-- SPDX-License-Identifier: Apache-2.0
import SpecTools.ScoreObservations
import SpecTools.Adversarial
import SpecTools.Discrimination

/-! Kernel-checked directions and independent human decisions for a versioned score journal. -/

namespace SpecTools.Score.Evidence
open Lean Elab Command Meta
open Observations

private structure FormalBinding where
  property : String
  reference : Name
  candidate : Name
  direction : Direction
  deriving FromJson

private structure ProofReference where
  observation : Name
  theoremName : Name
  deriving DecidableEq, FromJson

inductive Judgment where
  | accepted
  | rejected
  deriving DecidableEq, FromJson, ToJson

structure HumanDecision where
  evidenceId : String
  reviewer : String
  judgment : Judgment
  deriving FromJson, ToJson

private structure ReviewFile where
  version : Nat
  decisions : List HumanDecision
  deriving FromJson, ToJson

private def agree {α : Type} (compatible : α → α → Bool) (items : List α) : Option α := do
  let first ← items.head?
  if items.all (compatible first) then some first else none

private def attributed (first other : HumanDecision) : Bool :=
  !other.reviewer.trimAscii.isEmpty && decide (other.judgment = first.judgment)

def reviewed (decisions : List HumanDecision) : List HumanDecision :=
  if (agree attributed decisions).isSome then decisions else []

theorem reviewed_attributed (decisions : List HumanDecision) (decision : HumanDecision)
    (member : decision ∈ reviewed decisions) :
    decision ∈ decisions ∧ decision.reviewer.trimAscii.isEmpty = false := by
  cases first : decisions.head? with
  | none => simp [reviewed, agree, first] at member
  | some firstDecision =>
    simp [reviewed, agree, first] at member
    have evidence := member.1 decision member.2
    simp [attributed] at evidence
    exact ⟨member.2, evidence.1⟩

private def indexBy {α : Type} (identity : α → String) (items : List α) :
    Std.HashMap String (List α) :=
  items.foldr (fun item table => table.alter (identity item) fun prior =>
    some (item :: prior.getD [])) ∅

private def optionalField {α : Type} [FromJson α] (object : Json) (field : String) :
    Except String (Option α) :=
  match object.getObjVal? field with
  | .ok value => fromJson? value
  | .error _ => .ok none

private def indexBindings (plants : List Plant) (bindings : List FormalBinding) :
    Except String (Std.HashMap String FormalBinding) := do
  let properties := Std.HashSet.ofList (plants.map (·.property))
  let mut result := ∅
  for binding in bindings do
    unless properties.contains binding.property do
      throw "formal bindings must name a property in the protected key"
    if result.contains binding.property then
      throw "the protected key must supply at most one formal binding per property"
    result := result.insert binding.property binding
  return result

private def checked (binding : FormalBinding) (proof : ProofReference) :
    CommandElabM (Option Json) := do
  try
    let reference ← Adversarial.safeTerm binding.reference
    let candidate ← Adversarial.safeTerm binding.candidate
    let observation ← Adversarial.safeTerm proof.observation
    let direction := match binding.direction with
      | .admitsExtra => mkConst ``Direction.admitsExtra
      | .rejectsRequired => mkConst ``Direction.rejectsRequired
    let expected ← liftTermElabM <| mkAppM ``BoundDistinction #[
      toExpr binding.property, reference, candidate, direction, observation]
    Adversarial.requireProof proof.theoremName expected
    return some <| Json.mkObj [
      ("property", toJson binding.property), ("direction", toJson binding.direction),
      ("theoremName", toJson proof.theoremName), ("observation", toJson proof.observation)]
  catch _ =>
    return none

private def readJson (path : String) : CommandElabM Json := do
  ofExcept (Json.parse (← IO.FS.readFile path))

private def journal (keyRaw findingsRaw : Json) (reviewFile : Option ReviewFile) :
    CommandElabM Json := do
  let key : KeyFile ← ofExcept (fromJson? keyRaw)
  let findings : FindingsFile ← ofExcept (fromJson? findingsRaw)
  let summary ← ofExcept (report key findings)
  let raw : List Json ← ofExcept (findingsRaw.getObjValAs? _ "findings")
  let bindings : Option (List FormalBinding) ← ofExcept (optionalField keyRaw "formalBindings")
  let formalKey ← ofExcept (indexBindings key.plants (bindings.getD []))
  let human ← match reviewFile with
    | none => pure []
    | some reviews =>
      unless reviews.version == key.version do
        throwError "review input must match the key and finding version"
      pure reviews.decisions
  let reviews := indexBy HumanDecision.evidenceId human
  let proofRefs := indexBy Prod.fst <| (findings.findings.zip raw).map fun (finding, value) =>
    (finding.evidenceId, ((optionalField value "formal").toOption.join : Option ProofReference))
  let mut distinctions : Array Json := #[]
  let mut judgments : Array Json := #[]
  for finding in coherent findings.findings do
    let decisions := reviewed (reviews[finding.evidenceId]?.getD [])
    if let some decision := decisions.head? then
      let reviewers := (decisions.map (·.reviewer)).eraseDups
      judgments := judgments.push (Json.mkObj [
        ("evidenceId", toJson finding.evidenceId), ("judgment", toJson decision.judgment),
        ("reviewers", toJson reviewers)])
    let proposed := ((proofRefs[finding.evidenceId]?).getD []).map Prod.snd
    if let some (some proof) := agree (fun a b => decide (a = b)) proposed then
      if let some binding := finding.property.bind (fun id => formalKey[id]?) then
        if let some report ← checked binding proof then
          distinctions := distinctions.push (report.setObjVal! "evidenceId" (toJson finding.evidenceId))
  let roots := ((bindings.getD []).flatMap fun b => [b.reference, b.candidate]) ++
    (raw.flatMap fun j => ((optionalField j "formal").toOption.join : Option ProofReference).toList.flatMap
      (fun p => [p.theoremName, p.observation]))
  return SpecTools.Evidence.attach (← getEnv) "discrimination.v1"
    (toJson (keyRaw, findingsRaw, reviewFile, Adversarial.acceptedAxioms)) roots <|
    summary.setObjVal! "schema" "elenxis.discrimination.v1"
    |>.setObjVal! "findings" (toJson raw)
    |>.setObjVal! "distinguished" (if distinctions.isEmpty then toJson "unknown" else .arr distinctions)
    |>.setObjVal! "humanReviewed" (if judgments.isEmpty then toJson "unknown" else toJson judgments)

syntax "#score_journal" str str (" with " str)? : command

elab_rules : command
  | `(#score_journal $key:str $findings:str $[with $review:str]?) => do
    let independent ← review.mapM fun path => do
      ofExcept (fromJson? (← readJson path.getString))
    let result ← journal (← readJson key.getString) (← readJson findings.getString) independent
    IO.println result.compress

end SpecTools.Score.Evidence
