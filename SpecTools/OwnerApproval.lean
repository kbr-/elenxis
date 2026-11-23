import SpecTools.GapsRun

/-! A signed owner decision and a separate Lean check against the approved baseline. -/

namespace SpecTools.OwnerApproval
open Lean Elab Command
open SpecTools.Audit SpecTools.Gaps

structure ContractSnapshot where
  declaration : Name
  baseline : Name
  expression : String
  dependencies : List (Name × String)
  deriving BEq, DecidableEq, FromJson, ToJson

structure Snapshot where
  subject : String
  revision : String
  prose : String
  coverage : String
  toolchain : String
  contracts : List ContractSnapshot
  deriving BEq, DecidableEq, FromJson, ToJson

structure Receipt where
  version : Nat
  owner : String
  decisionId : String
  origin : String
  synthetic : Bool
  accepted : Bool
  snapshot : Snapshot
  deriving FromJson, ToJson

structure Files where
  subject : String
  revision : String
  prose : System.FilePath
  coverage : System.FilePath

structure SignatureFiles where
  owner : String
  receipt : System.FilePath
  signature : System.FilePath
  allowedSigners : System.FilePath

def accepts (owner : String) (current : Snapshot) (receipt : Receipt) (authenticated : Bool) : Bool :=
  authenticated && decide (receipt.version = 1) && decide (receipt.owner = owner) &&
    !receipt.decisionId.trimAscii.isEmpty && !receipt.origin.trimAscii.isEmpty &&
    receipt.accepted && decide (receipt.snapshot = current)

theorem accepts_iff (owner : String) (current : Snapshot) (receipt : Receipt) (authenticated : Bool) :
    accepts owner current receipt authenticated = true ↔
      authenticated = true ∧ receipt.version = 1 ∧ receipt.owner = owner ∧
      receipt.decisionId.trimAscii.isEmpty = false ∧ receipt.origin.trimAscii.isEmpty = false ∧
      receipt.accepted = true ∧ receipt.snapshot = current := by
  simp [accepts, Bool.and_eq_true, and_assoc]

private def decodeDraft (coverage : String) : CommandElabM (List DraftRow) :=
  ofExcept (Json.parse coverage >>= fromJson?)

/-- Traverse the definitions on which the snapshot can reduce, visiting each constant once. -/
private def dependencies (env : Environment) (roots : Array Name) : List (Name × String) := Id.run do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut result := []
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.drop 1
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let value := match info with
      | .defnInfo definition => some definition.value
      | _ => none
    result := (name, reprStr (info.levelParams, info.type, value)) :: result
    pending := info.type.getUsedConstants.toList ++
      (value.map (·.getUsedConstants.toList)).getD [] ++ pending
  return result.mergeSort (fun left right => left.1.toString ≤ right.1.toString)

/-- Read a review packet from a trusted baseline already elaborated by the current Lean process. -/
def capture (files : Files) (bindings : List ApprovedContract) : CommandElabM Snapshot := do
  if files.subject.trimAscii.isEmpty || files.revision.trimAscii.isEmpty then
    throwError "Owner review requires a subject and a revision."
  let coverage ← IO.FS.readFile files.coverage
  let draft ← decodeDraft coverage
  let issues := contractBindingIssues draft bindings
  unless issues.isEmpty && !bindings.isEmpty do
    throwError "Owner review needs complete contract bindings:\n{String.intercalate "\n" issues}"
  let env ← getEnv
  let contracts ← bindings.mapM fun binding => do
    let some (.defnInfo baseline) := env.find? binding.baseline
      | throwError "Missing owner-review baseline {binding.baseline}."
    let some fact ← factOf binding.baseline true
      | throwError "Cannot inspect owner-review baseline {binding.baseline}."
    unless fact.kind == .requirement && fact.unacceptedAxioms.isEmpty do
      throwError "Unsafe or conditional owner-review baseline {binding.baseline}."
    return ⟨binding.declaration, binding.baseline,
      reprStr (baseline.levelParams, baseline.type, baseline.value),
      dependencies env (baseline.type.getUsedConstants ++ baseline.value.getUsedConstants)⟩
  return ⟨files.subject, files.revision, ← IO.FS.readFile files.prose, coverage,
    Lean.versionString, contracts⟩

/-- The signature verifier consumes the exact JSON bytes that are decoded and compared below. -/
def checkOwner (current : Snapshot) (proof : SignatureFiles) : CommandElabM Receipt := do
  let bytes ← IO.FS.readFile proof.receipt
  let receipt : Receipt ← ofExcept (Json.parse bytes >>= fromJson?)
  let checked ← IO.Process.output { cmd := "ssh-keygen", args := #["-Y", "verify",
    "-f", proof.allowedSigners.toString, "-I", proof.owner, "-n", "elenxis-owner-approval-v1",
    "-s", proof.signature.toString] } (some bytes)
  unless checked.exitCode == 0 do
    throwError "Owner signature is absent, invalid, or unauthorized for {proof.owner}."
  unless accepts proof.owner current receipt true do
    throwError "Owner receipt does not accept the current requirements and baseline."
  IO.println (Json.mkObj [("ownerAcceptance", "verified"), ("owner", toJson receipt.owner),
    ("decisionId", toJson receipt.decisionId), ("origin", toJson receipt.origin),
    ("subject", toJson current.subject), ("revision", toJson current.revision),
    ("synthetic", toJson receipt.synthetic)]).compress
  return receipt

/-- Successful owner approval and successful definition comparison yield distinct receipts. -/
def check (files : Files) (bindings : List ApprovedContract) (proof : SignatureFiles) :
    CommandElabM Unit := do
  let current ← capture files bindings
  let _ ← checkOwner current proof
  checkApprovedContracts bindings
  IO.println (Json.mkObj [("contractMatch", "verified"), ("revision", toJson current.revision)]).compress

end SpecTools.OwnerApproval
