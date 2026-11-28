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
  deriving DecidableEq, ToJson, Inhabited

structure Attempt where
  challenge : Challenge
  certificate : Option Name := none
  deriving ToJson, Inhabited

inductive Variant where
  | named (declaration : Name)
  | dropLeftConjunct | dropRightConjunct | reverseImplication | dropPrecondition
  | alwaysTrue | alwaysFalse
  | toggleStrictness | raiseNatBoundary | lowerNatBoundary
  | toggleEquality | toggleQuantifier | negatePredicate
  deriving DecidableEq, ToJson, Inhabited

/-- An independently supplied review schedule pins both artifacts and the check requested. -/
structure ScheduledCheck where
  requirement : String
  revision : String
  id : String
  original : Name
  candidate : Variant
  challenge : Challenge
  deriving ToJson, Inhabited

/-- Construct a predicate in the local context of one observation. The original declaration
stays intact. A shape mismatch leaves the requested mutation invalid. -/
private def variantTerm (original : Expr) (variant : Variant) : MetaM Expr := do
  if let .named name := variant then
    Adversarial.safeTermMeta name
  else
    forallBoundedTelescope (← inferType original) (some 1) fun xs _ => do
      let #[x] := xs | throwError "Mutation requires a predicate over observations"
      let application := mkApp original x
      let surface := (← unfoldDefinition? application (ignoreTransparency := true)).getD application
      let body ← match variant with
        | .dropLeftConjunct | .dropRightConjunct | .reverseImplication | .dropPrecondition => whnf application
        | _ => pure surface.headBeta
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
        | .negatePredicate => mkAppM ``Not #[body]
        | .toggleEquality => do
          let op ← if body.isAppOfArity ``Eq 3 then pure ``Ne
            else if body.isAppOfArity ``Ne 3 then pure ``Eq else throwError "Expected equality or inequality"
          mkAppM op #[body.appFn!.appArg!, body.appArg!]
        | .toggleStrictness | .raiseNatBoundary | .lowerNatBoundary => do
          let strict := body.isAppOfArity ``LT.lt 4
          unless strict || body.isAppOfArity ``LE.le 4 do throwError "Expected an order comparison"
          let lhs := body.appFn!.appArg!
          let rhs := body.appArg!
          if variant == .toggleStrictness then
            mkAppM (if strict then ``LE.le else ``LT.lt) #[lhs, rhs]
          else
            unless ← isDefEq (← inferType rhs) (mkConst ``Nat) do throwError "Expected a Nat boundary"
            let shifted ← mkAppM (if variant == .raiseNatBoundary then ``Nat.succ else ``Nat.pred) #[rhs]
            pure (mkApp body.appFn! shifted)
        | .toggleQuantifier => do
          if let .forallE n domain inner bi := body then
            withLocalDecl n bi domain fun y => do
              mkAppM ``Exists #[← mkLambdaFVars #[y] (inner.instantiate1 y)]
          else if body.isAppOfArity ``Exists 2 then
            withLocalDeclD `y body.appFn!.appArg! fun y => mkForallFVars #[y] (mkApp body.appArg! y)
          else throwError "Expected an outer universal or existential quantifier"
        | .named _ => unreachable!
      mkLambdaFVars xs changed

/-- An owner can answer the question from the cited wording and the two outcomes.
A later clause may settle the question independently of the formal comparison. -/
structure OwnerQuestion where
  sourceClause : String
  alternativeClause : String
  originalOutcome : String
  alternativeOutcome : String
  question : String
  settlingClause : Option String := none
  deriving ToJson, Inhabited

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
  ownerQuestion : Option OwnerQuestion := none
  deriving ToJson, Inhabited

private def obligation (challenge : Challenge) (original candidate : Expr) : MetaM Expr := do
  let candidate ← match challenge with
    | .relation _ | .distinguishes .. => do
      unless ← isDefEq (← inferType original) (← inferType candidate) do
        throwError "The predicates must have a common observation domain"
      instantiateMVars candidate
    | _ => pure candidate
  match challenge with
  | .relation claim =>
    mkAppM ``Relation.Holds #[toExpr claim, original, candidate]
  | .distinguishes direction observation =>
    let sample ← Adversarial.safeTermMeta observation
    let direction := match direction with
      | .admitsExtra => mkConst ``Direction.admitsExtra
      | .rejectsRequired => mkConst ``Direction.rejectsRequired
    mkAppM ``Distinguishes #[original, candidate, direction, sample]
  | .satisfies | .refutes =>
    let law ← mkAppM' original #[candidate]
    unless ← isProp law do throwError "The law applied to the model must be a proposition"
    return if challenge matches .refutes then mkApp (mkConst ``Not) law else law

private def certificateResult (expected : Expr) (certificate : Name) : MetaM (String × String × List Name) := do
  try
    Adversarial.requireProofMeta certificate expected
    return ("established", "", (← collectAxioms certificate).toList)
  catch ex =>
    if ex.isInterrupt then throw ex
    return ("inconclusive", ← ex.toMessageData.toString, [])

private def assess (entry : Candidate) (attempt : Attempt) : MetaM Json := do
  let result (status : String) (reason : String) := Json.mkObj [
    ("challenge", toJson attempt.challenge), ("status", toJson status),
    ("certificate", toJson attempt.certificate), ("reason", toJson reason)]
  try
    let _ ← Adversarial.safeTermMeta entry.original
    let info ← getConstInfo entry.original
    let original := mkConst entry.original (info.levelParams.map Level.param)
    let candidate ← variantTerm original entry.candidate
    let expected ← obligation attempt.challenge original candidate
    let statement := (← ppExpr expected).pretty
    let some certificate := attempt.certificate
      | return (result "inconclusive" "No certificate supplied").setObjVal! "obligation" (toJson statement)
    let (status, reason, axioms) ← certificateResult expected certificate
    let checked := (result status reason).setObjVal! "obligation" (toJson statement)
    return if status == "established" then checked.setObjVal! "axioms" (toJson axioms) else checked
  catch ex =>
    if ex.isInterrupt then throw ex
    return result "invalid" (← ex.toMessageData.toString)

/-- A campaign checks the supplied candidates against the named declarations in this environment. -/
def review (entries : List Candidate) (schedule : Option (List ScheduledCheck) := none)
    (requirementsFile : Option System.FilePath := none) : CommandElabM Json := do
  let mut seen := ∅
  let mut records := #[]
  for entry in entries do
    let key := (entry.requirement, entry.revision, entry.id)
    if [entry.id, entry.requirement, entry.revision, entry.origin].any (·.trimAscii.isEmpty) then
      throwError "Each candidate needs a requirement, revision, ID and origin"
    if (seen : Std.HashSet (String × String × String)).contains key then
      throwError "Repeated candidate {entry.id} for {entry.requirement} at {entry.revision}"
    seen := seen.insert key
    let attempts ← entry.attempts.mapM fun a => liftTermElabM <| assess entry a
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
      ("ownerQuestion", toJson entry.ownerQuestion), ("assumptions", toJson entry.assumptions)]
  let missing := schedule.map fun planned => planned.filter fun p => !entries.any fun e =>
    p.requirement == e.requirement && p.revision == e.revision && p.id == e.id &&
    p.original == e.original && p.candidate == e.candidate && e.attempts.any (fun a => a.challenge == p.challenge)
  let roots := entries.flatMap fun e => [e.original] ++
    (match e.candidate with | .named n => [n] | _ => []) ++ (e.attempts.flatMap fun a =>
      a.certificate.toList ++ (match a.challenge with | .distinguishes _ n => [n] | _ => []))
  let source ← SpecTools.Evidence.requirementSource requirementsFile
  return SpecTools.Evidence.attach (← getEnv) "mutation.v1" (toJson (entries, schedule, Ledger.acceptedAxioms, source)) roots <|
    Json.mkObj [("schema", "elenxis.mutation.v1"), ("leanVersion", toJson Lean.versionString),
    ("missingScheduledChecks", toJson missing),
    ("sourceFile", toJson (← getFileName)),
    ("candidates", .arr records)]

end SpecTools.Mutation
