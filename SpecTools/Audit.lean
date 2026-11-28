-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Ledger
import SpecTools.Evidence

/-!
The audit: the ledger's rows judged against the Lean environment they're run in. This layer gathers
the facts (each named theorem's statement, axioms and hypotheses; the theorems written under the
project's module root; the modules the audit doesn't import) and prints the pure core's verdicts.
-/

namespace SpecTools.Audit
open Lean Elab Command Meta SpecTools.Ledger

/-- Existential closure of an already opened dependent telescope. -/
def existentialClosure (binders : Array Expr) : MetaM Expr := do
  let mut domain := mkConst ``True
  for binder in binders.reverse do
    let predicate ← mkLambdaFVars #[binder] domain
    domain ← mkAppM ``Exists #[predicate]
  return domain

private def proofTypeMatches (name : Name) (expected : Expr) : MetaM Bool :=
  withoutModifyingState do
    let proof ← mkConstWithFreshMVarLevels name
    isDefEq (← inferType proof) expected

private def scopeProposition (type : Expr) (contexts inputs : Nat) : MetaM (Option Expr) :=
  forallBoundedTelescope type (some (contexts + inputs)) fun xs _ => do
    if xs.size != contexts + inputs then return none
    let domain ← existentialClosure (xs.extract contexts xs.size)
    return some (← mkForallFVars (xs.extract 0 contexts) domain)

def inspectCertificate (name : Name) (expected : Expr) :
    CommandElabM (Bool × Option (List Name)) := do
  unless (← getEnv).find? name matches some (.thmInfo _) do return (false, none)
  let axioms := (← liftCoreM <| collectAxioms name).toList
  unless axioms.all acceptedAxioms.contains do return (false, some axioms)
  return (← liftTermElabM <| proofTypeMatches name expected, some axioms)

structure DomainObservation where
  subject : Name
  status : String
  proposition : Option String := none
  scope : Option DomainScope := none
  certificates : Array Json := #[]
  deriving ToJson

/-- Report the exact scoped proposition alongside its evidence even on cached rows. -/
def reportApplicability (rows : List Row) (strict : Bool)
    (observe : Nat → DomainObservation → CommandElabM Unit := fun _ _ => pure ()) :
    CommandElabM (List String) := do
  let mut issues := []
  for (row, index) in rows.zipIdx do
    for subject in row.theorems do
      unless row.applicability.any (·.subject == subject) do
        IO.println s!"  applicability {row.id} {subject}: unassessed"
        observe index { subject, status := "unassessed" }
    for claim in row.applicability do
      let label := s!"applicability {row.id} {claim.subject}"
      unless row.theorems.contains claim.subject do
        issues := issues ++ [s!"{label}: subject outside row"]
        continue
      let some (.thmInfo thm) := (← getEnv).find? claim.subject
        | issues := issues ++ [s!"{label}: expected theorem"]; continue
      let proposition ← match claim.scope with
        | .someInput n => liftTermElabM <| scopeProposition thm.type 0 n
        | .eachContext c n => liftTermElabM <| scopeProposition thm.type c n
        | .exclusion => pure (some thm.type)
        | .unsupported name =>
          let some (.defnInfo obligation) := (← getEnv).find? name
            | issues := issues ++ [s!"{label}: missing obligation definition {name}"]; continue
          unless ← liftTermElabM (isDefEq obligation.type (mkSort .zero)) do
            issues := issues ++ [s!"{label}: expected a proposition at {name}"]
            continue
          let body ← liftTermElabM <| ppExpr obligation.value
          IO.println s!"  {label}: unsupported obligation {name} ({body})"
          observe index {
            subject := claim.subject, scope := some claim.scope,
            status := "unsupported", proposition := some body.pretty }
          if strict then issues := issues ++ [s!"{label}: unsupported obligation {name}"]
          continue
      let some p := proposition
        | issues := issues ++ [s!"{label}: scope exceeds theorem telescope"]; continue
      let positive := match claim.scope with
        | .exclusion => claim.subject :: claim.supports
        | _ => claim.supports
      let mut supports := false
      let mut refutes := false
      let mut certificates := #[]
      for (names, negative) in [(positive, false), (claim.refutes, true)] do
        for proof in names do
          let (ok, axioms) ← inspectCertificate proof (if negative then mkApp (mkConst ``Not) p else p)
          certificates := certificates.push <| Json.mkObj [
            ("name", toJson proof), ("refutes", toJson negative), ("accepted", toJson ok),
            ("axioms", toJson axioms)]
          IO.println s!"  {label}: {if ok then "checked" else "rejected"} {proof} ({if negative then "against" else "for"})"
          if negative then refutes := refutes || ok else supports := supports || ok
      let result := domainResult supports refutes
      let status := match result with
        | .established => "established"
        | .refuted => "refuted"
        | .unresolved => "unresolved"
        | .conflicting => "conflicting evidence"
      let statement ← liftTermElabM <| withOptions (·.setBool `pp.explicit true) (ppExpr p)
      IO.println s!"  {label}: {status} ({statement})"
      observe index {
        subject := claim.subject, scope := some claim.scope, status,
        proposition := some statement.pretty, certificates }
      if result == .conflicting || (strict && result != .established) then
        issues := issues ++ [s!"{label}: {status}"]
  return issues

private def underRoot (env : Environment) (root : Name) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == root
  | none => true

/-- Theorems written in a source file under `root`, without the ones Lean generates. -/
def writtenTheorems (env : Environment) (root : Name) : CommandElabM (List Name) := do
  let candidates := env.constants.fold (init := []) fun found name info =>
    if info matches .thmInfo _ && !name.isInternal && underRoot env root name &&
        !env.isProjectionFn name then name :: found
    else found
  candidates.filterM fun name => return (← findDeclarationRanges? name).isSome

/-- The source modules under `dir` that the environment doesn't hold. -/
def missingModules (env : Environment) (dir : System.FilePath) : CommandElabM (List String) := do
  let files ← dir.walkDir
  let names := files.toList.filterMap fun file =>
    if file.extension == some "lean" then
      some <| (file.withExtension "").components.foldl (fun name part => name.str part) .anonymous
    else none
  return (names.filter (!env.header.moduleNames.contains ·)).map toString

/-- What the environment says of a name. -/
def factOf (name : Name) (requirements : Bool := false) : CommandElabM (Option Fact) := do
  match (← getEnv).find? name with
  | some (.thmInfo info) =>
    let statement := toString (← liftTermElabM <| ppExpr info.type)
    let axioms := (← liftCoreM <| collectAxioms name).toList
    let hypotheses ← liftTermElabM <| forallTelescope info.type fun xs _ =>
      xs.anyM fun x => do isProp (← inferType x)
    return some { statement, axioms, hypotheses }
  | some info =>
    if !requirements then return none
    let isProposition ← liftTermElabM <| forallTelescope info.type fun parameters _ =>
      isProp (mkAppN (mkConst name (info.levelParams.map Level.param)) parameters)
    let kind := requirementKind isProposition info.value?.isSome info.isUnsafe
    let statement ← liftTermElabM <| ppExpr (info.value?.getD info.type)
    let axioms := (← liftCoreM <| collectAxioms name).toList
    return some { statement := toString statement, axioms, hypotheses := false, kind }
  | none => return none

private def bindingChecks (facts : Facts) (binding : EvidenceBinding) : CommandElabM Bool := do
  let some subject := facts binding.subject | return false
  let some proof := facts binding.proofName | return false
  unless subject.kind == .theoremStatement && subject.hypotheses &&
      proof.kind == .theoremStatement && proof.unacceptedAxioms.isEmpty do
    return false
  let some (.thmInfo info) := (← getEnv).find? binding.subject | return false
  liftTermElabM do
    let domain ← forallTelescope info.type fun binders _ => existentialClosure binders
    let expected := match binding.kind with
      | .inhabited => domain
      | .inconsistent => mkApp (mkConst ``Not) domain
    proofTypeMatches binding.proofName expected

/-- Read declaration facts and check distinct proposed bindings in the current environment. -/
def inspectRows (rows : List Row) (requirements : Bool) : CommandElabM (Facts × CheckedEvidence) := do
  let bindings := (rows.flatMap (·.evidence)).eraseDups
  let names := ((rows.flatMap fun r => r.theorems ++ r.witnesses) ++
    bindings.map (·.proofName)).eraseDups
  let table ← names.filterMapM fun name => do
    return (← factOf name requirements).map (name, ·)
  let facts : Facts := fun name => table.lookup name
  let verified ← bindings.filterM (bindingChecks facts)
  return (facts, fun binding => decide (binding ∈ verified))

structure ApprovedContract where
  declaration : Name
  baseline : Name

/-- Property (approved theorem contracts): an actual theorem's elaborated proposition matches a
separate safe nullary Prop baseline; definitions retain their type-and-body comparison. -/
def contractIssue (contract : ApprovedContract) : CommandElabM (Option String) := do
  let actual := contract.declaration
  let expected := contract.baseline
  if actual == expected then return some s!"{actual}: baseline must be a separate declaration"
  let env ← getEnv
  let some (.defnInfo expectedInfo) := env.find? expected
    | return some s!"{expected}: missing approved baseline definition"
  let some expectedFact ← factOf expected true
    | return some s!"{expected}: cannot inspect approved baseline"
  if expectedFact.kind != .requirement then
    return some s!"{expected}: baseline must state a safe requirement"
  match env.find? actual with
  | some (.defnInfo actualInfo) =>
    let some actualFact ← factOf actual true
      | return some s!"{actual}: cannot inspect requirement"
    if actualFact.kind != .requirement then
      return some s!"{actual}: both definitions must state safe requirements"
    if actualInfo.levelParams.length != expectedInfo.levelParams.length then
      return some s!"{actual}: universe parameters differ from {expected}"
    let levels := expectedInfo.levelParams.map Level.param
    let actualType := actualInfo.type.instantiateLevelParams actualInfo.levelParams levels
    let actualBody := actualInfo.value.instantiateLevelParams actualInfo.levelParams levels
    let agrees ← liftTermElabM do
      if ← isDefEq actualType expectedInfo.type then isDefEq actualBody expectedInfo.value
      else pure false
    return if agrees then none else some s!"{actual}: differs from approved contract {expected}"
  | some (.thmInfo actualInfo) =>
    let baselineIsProp ← liftTermElabM <| isDefEq expectedInfo.type (mkSort levelZero)
    unless baselineIsProp do
      return some s!"{expected}: theorem baseline must be a nullary Prop definition"
    if actualInfo.levelParams.length != expectedInfo.levelParams.length then
      return some s!"{actual}: universe parameters differ from {expected}"
    let levels := expectedInfo.levelParams.map Level.param
    let actualType := actualInfo.type.instantiateLevelParams actualInfo.levelParams levels
    let agrees ← liftTermElabM <| isDefEq actualType expectedInfo.value
    return if agrees then none else some s!"{actual}: differs from approved contract {expected}"
  | _ => return some s!"{actual}: missing requirement definition or theorem"

def checkApprovedContracts (contracts : List ApprovedContract) : CommandElabM Unit := do
  if contracts.isEmpty then throwError "The approved contract list is empty."
  let issues ← contracts.filterMapM contractIssue
  unless issues.isEmpty do
    throwError "Specification differs from the approved Coverage draft:\n{String.intercalate "\n" issues}"
  IO.println s!"{contracts.length} specification declarations match their approved contracts."

/-- Explicit scopes replace the legacy positive-witness heuristic for the named subject.
Other premises, axioms and structural findings still go through the original gate. -/
def rowAuditIssues (requirements : Bool) (facts : Facts) (rows : List Row)
    (checked : CheckedEvidence)
    (observe : Nat → DomainObservation → CommandElabM Unit := fun _ _ => pure ()) :
    CommandElabM (List String) := do
  let domainIssues ← reportApplicability rows requirements observe
  unless requirements do return domainIssues
  let legacy := (specificationFindings facts rows checked).filter fun finding =>
    match finding with
    | .missingWitness id => rows.any fun row => row.id == id && missingLegacyWitness facts row checked
    | _ => true
  return legacy.map SpecificationFinding.render ++ domainIssues

private def digestVersion : String := "spec-tools premise evidence v2"

/-- Read versioned digests. Missing and earlier formats require a fresh audit. -/
def readDigests (path : System.FilePath) : IO (List (String × UInt64)) := do
  unless ← path.pathExists do return []
  let lines ← IO.FS.lines path
  if lines[0]? != some digestVersion then return []
  return (lines.toList.drop 1).filterMap fun line =>
    match line.splitOn " " with
    | [id, d] => d.toNat?.map fun n => (id, n.toUInt64)
    | _ => none

def writeDigests (path : System.FilePath) (ds : List (String × UInt64)) : IO Unit :=
  IO.FS.writeFile path (digestVersion ++ "\n" ++ String.join (ds.map fun (id, d) => s!"{id} {d}\n"))

private def declarationEvidence (facts : Facts) (name : Name) : Json :=
  match facts name with
  | none => Json.mkObj [("name", toJson name), ("formal", "unavailable"), ("trust", Json.null)]
  | some f =>
    let formal := match f.kind with
      | .theoremStatement => "kernel-checked theorem"
      | .requirement => "specified (unproved)"
      | .notProposition => "not a proposition"
      | .unavailableBody => "unavailable body"
    Json.mkObj [("name", toJson name), ("formal", toJson formal), ("statement", toJson f.statement),
      ("trust", Json.mkObj [("axioms", toJson f.axioms), ("unacceptedAxioms", toJson f.unacceptedAxioms)])]

structure RowEvidence where
  id : String
  clause : String
  source : String
  legacyVerdict : String
  declarations : List Json
  witnesses : List Json
  premiseEvidence : List Json
  applicability : Array DomainObservation
  ledgerStatus : String
  ledgerComment : String
  semanticCorrespondence : String := "unassessed"
  adversarialValidation : String := "unassessed"
  ownerApproval : String := "unassessed"
  deriving ToJson

/-- Ordinary audit inspects Lean declarations. Reviews performed by other commands have their own
receipts and cannot be inferred from the ledger annotation or the legacy verdict. -/
def rowEvidence (row : Row) (facts : Facts) (checked : CheckedEvidence)
    (domains : Array DomainObservation) : RowEvidence :=
  let annotation := match row.status with
    | .covered => ("covered", "")
    | .uncovered reason => ("uncovered", reason)
    | .provisional reason => ("provisional", reason)
    | .accepted reason => ("accepted", reason)
  { id := row.id, clause := row.clause, source := row.source
    legacyVerdict := (verdict facts row checked).label
    declarations := row.theorems.map (declarationEvidence facts)
    witnesses := row.witnesses.map (declarationEvidence facts)
    premiseEvidence := row.evidence.map fun b => Json.mkObj [
      ("subject", toJson b.subject), ("kind", toJson b.kind.label), ("proof", declarationEvidence facts b.proofName),
      ("accepted", toJson (row.theorems.contains b.subject && checked b))]
    applicability := domains, ledgerStatus := annotation.1, ledgerComment := annotation.2 }

theorem ordinaryAudit_review_scope (row : Row) (facts : Facts) (checked : CheckedEvidence)
    (domains : Array DomainObservation) :
    let evidence := rowEvidence row facts checked domains
    evidence.semanticCorrespondence = "unassessed" ∧ evidence.adversarialValidation = "unassessed" ∧
    evidence.ownerApproval = "unassessed" := by
  exact ⟨rfl, rfl, rfl⟩

def rowManifest (rows : List Row) : CommandElabM (Option Evidence.Manifest) := do
  let manifest ← Evidence.readManifest
  if let some m := manifest then
    for row in rows do
      unless m.requirements.any (fun r => r.id == row.id && r.clause == row.clause &&
          row.theorems.all r.declarations.contains) do
        throwError "Evidence manifest differs from ledger row {row.id}"
  return manifest

def evidenceRoots (rows : List Row) : List Name := rows.flatMap fun row =>
  row.theorems ++ row.witnesses ++ (row.evidence.flatMap fun b => [b.subject, b.proofName]) ++
    (row.applicability.flatMap fun c => [c.subject] ++ c.supports ++ c.refutes ++
      (match c.scope with | .unsupported n => [n] | _ => []))

/-- Judge the ledger's rows and print each verdict with the statements and axioms behind it. Fails
on what makes the report wrong: a repeated identifier, a named theorem that is no theorem, a written
theorem no row claims, a source module the audit doesn't import. A row not stated, conditional or
too weak fails nothing: the report exists to show it. With `digestFile`, rows whose clause and named
statements are unchanged since the last run are listed as unchanged and not re-judged. -/
def run (rows : List Row) (root : Name) (sourceDir : Option System.FilePath := none)
    (digestFile : Option System.FilePath := none) (requirements : Bool := false)
    (emitEvidence : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let (facts, checked) ← inspectRows rows requirements
  let stored ← match digestFile with
    | some p => readDigests p
    | none => pure []
  let judged := toRejudge stored facts rows checked
  let mut errors : List String := (repeatedIds rows).map (s!"row {·} is listed twice")
  let observations ← IO.mkRef ({} : Std.HashMap Nat (Array DomainObservation))
  errors := errors ++ (← rowAuditIssues requirements facts rows checked fun id obs => do
    if emitEvidence then observations.modify fun table => table.insert id ((table.getD id #[]).push obs))
  IO.println "Audit scope: declarations, axiom dependencies and premise evidence. Semantic correspondence, adversarial validation and owner approval: unassessed by this run."
  let mut counts : List (String × Nat) := []
  for row in rows do
    if !judged.any (·.id == row.id) then
      IO.println s!"unchanged: {row.id}"
      continue
    let v := verdict facts row checked
    if let .missing n := v then errors := errors ++ [s!"{row.id} names {n}, which is no theorem"]
    counts := match counts.lookup v.label with
      | some k => (v.label, k + 1) :: counts.filter (·.1 != v.label)
      | none => (v.label, 1) :: counts
    let verdictLabel := if row.applicability.isEmpty then v.label else s!"legacy verdict: {v.label}"
    IO.println s!"{verdictLabel}: {row.id}: {row.clause}"
    for n in row.theorems ++ row.witnesses do
      if let some f := facts n then
        IO.println s!"  {n} : {f.statement}"
        IO.println s!"    axioms: {f.axioms}"
    for binding in row.evidence do
      let valid := row.theorems.contains binding.subject && checked binding
      let result := if valid then "checked" else "rejected"
      IO.println s!"  {result} {binding.kind.label} evidence: {binding.proofName} for {binding.subject}"
      if let some proof := facts binding.proofName then
        IO.println s!"    {proof.statement}"
        IO.println s!"    axioms: {proof.axioms}"
  for n in unclaimed rows (← writtenTheorems env root) do
    errors := errors ++ [s!"no row claims theorem {n}"]
  if let some dir := sourceDir then
    for m in ← missingModules env dir do
      errors := errors ++ [s!"the audit does not import module {m}"]
  let count (label : String) := (counts.lookup label).getD 0
  if emitEvidence then
    let domains ← observations.get
    let report := Json.mkObj [("schema", "elenxis.audit.v1"), ("requirementsMode", toJson requirements),
      ("acceptedAxioms", toJson acceptedAxioms), ("issues", toJson errors),
      ("rows", toJson (rows.zipIdx.map fun (row, index) => rowEvidence row facts checked (domains.getD index #[])))]
    let roots := evidenceRoots rows
    let inputs := toJson (reprStr rows, root, sourceDir.map toString, requirements, acceptedAxioms, errors)
    IO.println (← Evidence.attachWith (← rowManifest rows) `SpecTools.Audit.run "audit.v1" inputs roots report).compress
  IO.println s!"{rows.length} rows: {count "proved"} proved{specificationSuffix requirements (count "specified (unproved)")}, \
    {count "conditional"} conditional, \
    {count "unknown nonvacuity"} unknown nonvacuity, \
    {count "inconsistent premises"} inconsistent premises, {count "not stated"} not stated \
    ({judged.length} judged)"
  if let some p := digestFile then
    if errors.isEmpty then writeDigests p (digests facts rows checked)
  unless errors.isEmpty do
    throwError "audit failed:\n{"\n".intercalate errors}"

end SpecTools.Audit
