-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Adversarial
import SpecTools.Discrimination

namespace SpecTools.Mutation
open Lean Elab Command Meta Score.Evidence

/-- Each requested result identifies the proposition for which a certificate is needed. -/
inductive Challenge where
  | relation (claim : Relation)
  | distinguishes (direction : Direction) (observation : Name)
  | satisfies
  | refutes
  deriving ToJson, Inhabited

structure Attempt where
  challenge : Challenge
  certificate : Option Name := none
  deriving Inhabited

inductive Variant where
  | named (declaration : Name)
  | dropLeftConjunct | dropRightConjunct | reverseImplication | dropPrecondition
  | alwaysTrue | alwaysFalse
  deriving ToJson, Inhabited

/-- Construct a predicate in the local context of one observation. The original declaration
stays intact. A shape mismatch leaves the requested mutation invalid. -/
private def variantTerm (original : Expr) (variant : Variant) : CommandElabM Expr := do
  if let .named name := variant then return ← Adversarial.safeTerm name
  liftTermElabM do
    forallBoundedTelescope (← inferType original) (some 1) fun xs _ => do
      let #[x] := xs | throwError "Mutation requires a predicate over observations"
      let body ← whnf (mkApp original x)
      unless ← isProp body do throwError "Mutation requires a proposition-valued predicate"
      let changed ← match variant with
        | .dropLeftConjunct | .dropRightConjunct => do
          unless body.isAppOfArity ``And 2 do throwError "Expected a conjunction"
          pure (if variant matches .dropLeftConjunct then body.appArg! else body.appFn!.appArg!)
        | .reverseImplication | .dropPrecondition => do
          let .forallE _ premise consequence _ := body | throwError "Expected an implication"
          unless (← isProp premise) && !consequence.hasLooseBVars do
            throwError "Expected a nondependent implication"
          if variant matches .dropPrecondition then pure consequence else mkArrow consequence premise
        | .alwaysTrue => pure (mkConst ``True)
        | .alwaysFalse => pure (mkConst ``False)
        | .named _ => unreachable!
      mkLambdaFVars xs changed

structure Candidate where
  id : String
  requirement : String
  revision : String
  origin : String
  original : Name
  candidate : Variant
  attempts : List Attempt
  scenario : String := ""
  suspectedWeakness : String := ""
  proposedProperty : String := ""
  assumptions : List String := []
  deriving Inhabited

private def obligation (challenge : Challenge) (original candidate : Expr) : CommandElabM Expr := do
  match challenge with
  | .relation claim =>
    liftTermElabM <| mkAppM ``Relation.Holds #[toExpr claim, original, candidate]
  | .distinguishes direction observation =>
    let sample ← Adversarial.safeTerm observation
    let direction := match direction with
      | .admitsExtra => mkConst ``Direction.admitsExtra
      | .rejectsRequired => mkConst ``Direction.rejectsRequired
    liftTermElabM <| mkAppM ``Distinguishes #[original, candidate, direction, sample]
  | .satisfies | .refutes =>
    let law ← liftTermElabM <| mkAppM' original #[candidate]
    unless ← liftTermElabM (isProp law) do throwError "The law applied to the model must be a proposition"
    return if challenge matches .refutes then mkApp (mkConst ``Not) law else law

private def certificateResult (expected : Expr) (certificate : Name) : CommandElabM (String × String × List Name) := do
  try
    Adversarial.requireProof certificate expected
    return ("established", "", (← liftCoreM <| collectAxioms certificate).toList)
  catch ex =>
    if ex.isInterrupt then throw ex
    return ("inconclusive", ← ex.toMessageData.toString, [])

private def assess (entry : Candidate) (attempt : Attempt) : CommandElabM Json := do
  let result (status : String) (reason : String) := Json.mkObj [
    ("challenge", toJson attempt.challenge), ("status", toJson status),
    ("certificate", toJson attempt.certificate), ("reason", toJson reason)]
  try
    let _ ← Adversarial.safeTerm entry.original
    let info ← getConstInfo entry.original
    let original := mkConst entry.original (info.levelParams.map Level.param)
    let candidate ← variantTerm original entry.candidate
    let expected ← obligation attempt.challenge original candidate
    let statement := (← liftTermElabM <| ppExpr expected).pretty
    let some certificate := attempt.certificate
      | return (result "inconclusive" "No certificate supplied").setObjVal! "obligation" (toJson statement)
    let (status, reason, axioms) ← certificateResult expected certificate
    let checked := (result status reason).setObjVal! "obligation" (toJson statement)
    return if status == "established" then checked.setObjVal! "axioms" (toJson axioms) else checked
  catch ex =>
    if ex.isInterrupt then throw ex
    return result "invalid" (← ex.toMessageData.toString)

/-- A campaign checks the supplied candidates against the named declarations in this environment. -/
def review (entries : List Candidate) : CommandElabM Json := do
  let mut seen := ∅
  let mut records := #[]
  for entry in entries do
    let key := (entry.requirement, entry.revision, entry.id)
    if [entry.id, entry.requirement, entry.revision, entry.origin].any (·.trimAscii.isEmpty) then
      throwError "Each candidate needs a requirement, revision, ID and origin"
    if (seen : Std.HashSet (String × String × String)).contains key then
      throwError "Repeated candidate {entry.id} for {entry.requirement} at {entry.revision}"
    seen := seen.insert key
    let attempts ← entry.attempts.mapM (assess entry)
    let definition (name : Name) := do
      let some info := (← getEnv).find? name | return Json.null
      let some body := info.value? (allowOpaque := true) | return Json.null
      return toJson (← liftTermElabM <| ppExpr body).pretty
    let candidateBody ← match entry.candidate with
      | .named name => definition name
      | _ => pure Json.null
    records := records.push <| Json.mkObj [
      ("id", toJson entry.id), ("requirement", toJson entry.requirement), ("revision", toJson entry.revision),
      ("origin", toJson entry.origin), ("original", toJson entry.original), ("candidate", toJson entry.candidate),
      ("originalDefinition", ← definition entry.original), ("namedCandidateDefinition", candidateBody),
      ("attempted", toJson (!attempts.isEmpty)), ("checks", toJson attempts), ("scenario", toJson entry.scenario),
      ("suspectedWeakness", toJson entry.suspectedWeakness), ("proposedProperty", toJson entry.proposedProperty),
      ("assumptions", toJson entry.assumptions)]
  return Json.mkObj [("schema", "elenxis.mutation.v1"), ("leanVersion", toJson Lean.versionString),
    ("sourceFile", toJson (← getFileName)),
    ("candidates", .arr records)]

end SpecTools.Mutation
