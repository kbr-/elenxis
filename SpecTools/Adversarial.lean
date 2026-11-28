-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Audit

/-!
Typed adversarial admission. A semantic claim is checked against the actual law and
implementation; its counterexample must prove the negation of that same law for the named
mutant. Hypothesis witnesses inhabit the existential closure of the claim's binders.
Inventory uses Lean's declaration ranges, not a search for theorem-looking text.
-/

namespace SpecTools.Adversarial

open Lean Elab Command Meta

register_option specTools.adversarial.root : String := {
  defValue := ""
  descr := "Require typed adversarial coverage of every source theorem under this module root"
}

initialize auditedNames : EnvExtension NameSet ← registerEnvExtension (pure {})

structure Attack where
  description : String
  mutant : Name
  refutation : Name
  deriving Inhabited

structure SemanticEntry where
  theoremName : Name
  law : Name
  implementation : Name
  witness : Name
  attacks : List Attack
  deriving Inhabited

structure SupportingEntry where
  theoremName : Name
  parent : Name
  law : Name
  implementation : Name
  witness : Name
  mutant : Name
  survival : Name
  survivingModel : String
  deriving Inhabited

def acceptedAxioms : List Name := Ledger.acceptedAxioms

def proofIssues (name : Name) : CommandElabM (List String) := do
  let env ← getEnv
  let some (.thmInfo _) := env.find? name
    | return [s!"{name}: evidence must be a proved theorem"]
  let axioms := (← liftCoreM <| collectAxioms name).toList
  return (axioms.filter (!acceptedAxioms.contains ·)).map fun axiomName =>
    s!"{name}: unaccepted axiom {axiomName}"

def safeTerm (name : Name) : CommandElabM Expr := do
  let some info := (← getEnv).find? name
    | throwError "Missing admission declaration {name}"
  if info.isUnsafe || (info.value? (allowOpaque := true)).isNone then
    throwError "{name}: admission terms need safe, inspectable bodies"
  liftTermElabM <| mkConstWithFreshMVarLevels name

def requireProof (name : Name) (expected : Expr) : CommandElabM Unit := do
  let issues ← proofIssues name
  unless issues.isEmpty do throwError "{String.intercalate "; " issues}"
  let proof ← safeTerm name
  let agrees ← liftTermElabM do isDefEq (← inferType proof) expected
  unless agrees do
    let actual ← liftTermElabM do ppExpr (← inferType proof)
    let wanted ← liftTermElabM <| ppExpr expected
    throwError "{name}: evidence has the wrong type\nActual: {actual}\nRequired: {wanted}"

def hypothesisType (statement : Expr) : MetaM Expr :=
  forallTelescopeReducing statement fun binders _ => Audit.existentialClosure binders

def lawAt (entry : SemanticEntry) (implementation : Name) : CommandElabM Expr := do
  let law ← safeTerm entry.law
  let model ← safeTerm implementation
  let statement ← liftTermElabM <| mkAppM' law #[model]
  unless ← liftTermElabM <| isProp statement do
    throwError "{entry.law}: the applied law is not a proposition"
  return statement

def preflight (entry : SemanticEntry) : CommandElabM Unit := do
  if entry.attacks.isEmpty then
    throwError "{entry.theoremName}: no cheapest-wrong-model refutation supplied"
  let expected ← lawAt entry entry.implementation
  let domain ← liftTermElabM <| hypothesisType expected
  requireProof entry.witness domain
  for attack in entry.attacks do
    if attack.description.trimAscii.toString.isEmpty then
      throwError "{entry.theoremName}: the wrong-model description is empty"
    let bad ← lawAt entry attack.mutant
    let rejected ← liftTermElabM <| mkAppM ``Not #[bad]
    requireProof attack.refutation rejected
  IO.println s!"Adversarial preflight: {entry.theoremName}; {entry.attacks.length} typed refutations"

def checkSemantic (entry : SemanticEntry) : CommandElabM Unit := do
  preflight entry
  requireProof entry.theoremName (← lawAt entry entry.implementation)

syntax (name := adversarialClaim) "adversarial_claim " term " in " command : command

def checkWrapped (entry : SemanticEntry) (actual : Name) : CommandElabM Unit := do
  unless entry.theoremName == actual do
    throwError "Adversarial claim names {entry.theoremName}, but wrapped theorem is {actual}"
  checkSemantic entry

@[command_elab adversarialClaim]
def elaborateClaim : CommandElab := fun stx => do
  let `(adversarial_claim $entrySyntax:term in $declaration:command) := stx
    | throwUnsupportedSyntax
  unless declaration.raw.isOfKind ``Lean.Parser.Command.declaration &&
      declaration.raw[1].isOfKind ``Lean.Parser.Command.theorem do
    throwError "adversarial_claim requires one theorem declaration"
  elabCommand (← `(command| run_cmd preflight $entrySyntax))
  if (← get).messages.hasErrors then return
  elabCommand declaration
  if (← get).messages.hasErrors then return
  let actual ← resolveGlobalConstNoOverload declaration.raw[1][1][0]
  elabCommand (← `(command| run_cmd checkWrapped $entrySyntax $(quote actual)))

def checkSupporting (entry : SupportingEntry) (semantics : List SemanticEntry) : CommandElabM Unit := do
  let some parent := semantics.find? (fun parent => parent.theoremName == entry.parent)
    | throwError "{entry.theoremName}: no admitted semantic parent {entry.parent}"
  checkSemantic parent
  unless parent.implementation == entry.implementation &&
      parent.attacks.any (fun attack => attack.mutant == entry.mutant) do
    throwError "{entry.theoremName}: supporting law and semantic parent must share implementation and mutant"
  if entry.survivingModel.trimAscii.toString.isEmpty then
    throwError "{entry.theoremName}: disclose the cheap model this supporting law alone admits"
  let issues ← proofIssues entry.theoremName
  unless issues.isEmpty do throwError "{String.intercalate "; " issues}"
  let semantic : SemanticEntry := {
    theoremName := entry.theoremName
    law := entry.law
    implementation := entry.implementation
    witness := entry.witness
    attacks := [] }
  let statement ← lawAt semantic entry.implementation
  requireProof entry.theoremName statement
  requireProof entry.survival (← lawAt semantic entry.mutant)
  let domain ← liftTermElabM <| hypothesisType statement
  requireProof entry.witness domain

def sourceTheorems (root : Name) : CommandElabM (List Name) := do
  let env ← getEnv
  let collect := fun (found : List Name) (name : Name) (info : ConstantInfo) =>
    if info matches .thmInfo _ &&
        !(privateToUserName name).isInternal && !env.isProjectionFn name then name :: found
    else found
  let mut imported := []
  for (moduleInfo, data) in env.header.modules.zip env.header.moduleData do
    if moduleInfo.module.getRoot == root then
      imported := data.constants.foldl (fun found info => collect found info.name info) imported
  let candidates := env.constants.foldStage2 collect imported
  candidates.filterM fun name => return (← findDeclarationRanges? name).isSome

def inventory (root : Name) : CommandElabM (Array Json) := do
  let env ← getEnv
  let names ← sourceTheorems root
  let sorted := names.mergeSort fun a b => a.toString < b.toString
  sorted.toArray.mapM fun name => do
    let some fact ← Audit.factOf name | throwError "Cannot inspect theorem {name}"
    let some ranges ← findDeclarationRanges? name | throwError "Missing source range for {name}"
    let moduleName := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]!.toString
      | none => env.mainModule.toString
    return Json.mkObj [
      ("name", toJson name.toString), ("sourceName", toJson (privateToUserName name).toString),
      ("module", toJson moduleName),
      ("line", toJson ranges.range.pos.line), ("statement", toJson fact.statement),
      ("hasHypotheses", toJson fact.hypotheses),
      ("axioms", toJson (fact.axioms.map toString))]

def audit (root : Name) (semantics : List SemanticEntry) (supporting : List SupportingEntry)
    (emitEvidence : Bool := false) : CommandElabM Unit := do
  if semantics.isEmpty then throwError "No semantic contracts admitted"
  let claims := semantics.map (·.theoremName) ++ supporting.map (·.theoremName)
  if claims.eraseDups.length != claims.length then throwError "Duplicate theorem admission entries"
  let evidence := (semantics.flatMap fun entry => entry.witness :: entry.attacks.map (·.refutation)) ++
    (supporting.flatMap fun entry => [entry.witness, entry.survival])
  let covered := claims ++ evidence
  let names ← sourceTheorems root
  let missing := names.filter (!covered.contains ·)
  unless missing.isEmpty do
    throwError "Theorems without adversarial admission: {String.intercalate ", " (missing.map toString)}"
  for entry in semantics do checkSemantic entry
  for entry in supporting do checkSupporting entry semantics
  modifyEnv fun env => auditedNames.modifyState env fun admitted =>
    covered.foldl (fun names name => names.insert name) admitted
  IO.println s!"Adversarial audit: {names.length} written theorems covered"
  if emitEvidence then
    let rejected := semantics.flatMap fun entry => entry.attacks.map fun attack => Json.mkObj [
      ("subject", toJson entry.theoremName), ("law", toJson entry.law), ("model", toJson attack.mutant),
      ("status", "refuted"), ("certificate", toJson attack.refutation)]
    let satisfying := supporting.map fun entry => Json.mkObj [
      ("subject", toJson entry.theoremName), ("law", toJson entry.law), ("model", toJson entry.mutant),
      ("status", "satisfies"), ("certificate", toJson entry.survival)]
    IO.println (Json.mkObj [("schema", "elenxis.adversarial.v1"), ("root", toJson root),
      ("sourceTheorems", toJson names), ("checkedClaims", toJson (rejected ++ satisfying))]).compress

def enforceCoverage : CommandElabM Unit := do
  let root := specTools.adversarial.root.get (← getOptions)
  unless root.isEmpty do
    let env ← getEnv
    let admitted := auditedNames.getState env
    let missing := (← sourceTheorems (.mkSimple root)).filter (!admitted.contains ·)
    unless missing.isEmpty do
      throwError "Automatic adversarial admission: unchecked theorems: {String.intercalate ", " (missing.map toString)}"

initialize addModuleLinter {
  name := ``enforceCoverage
  run := fun _ => enforceCoverage
}

end SpecTools.Adversarial
