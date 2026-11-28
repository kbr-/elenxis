-- SPDX-License-Identifier: Apache-2.0
import Lean

namespace SpecTools.Evidence
open Lean

structure Fingerprint where
  version : String
  producer : String
  inputs : String
  declarations : String
  build : String
  deriving ToJson, FromJson, DecidableEq

def freshness (saved current : Option Fingerprint) : String :=
  match saved, current with
  | some a, some b => if a = b then "current" else "stale"
  | _, _ => "unknown"

theorem current_iff (saved current : Option Fingerprint) :
    freshness saved current = "current" ↔ ∃ key, saved = some key ∧ current = some key := by
  cases saved <;> cases current <;> simp [freshness]
  exact eq_comm

private def kindKey : ConstantInfo → UInt64
  | .defnInfo _ => hash "definition"
  | .thmInfo _ => hash "theorem"
  | .opaqueInfo _ => hash "opaque"
  | .axiomInfo _ => hash "axiom"
  | .quotInfo _ => hash "quotient"
  | .inductInfo i => hash ("inductive", i.all, i.ctors, i.numParams, i.numIndices, i.isRec)
  | .ctorInfo c => hash ("constructor", c.induct, c.cidx, c.numFields)
  | .recInfo r => hash ("recursor", r.k, r.rules.map fun rule => (rule.ctor, rule.nfields, rule.rhs))

/-- Content marker for replay in a trusted environment. Each reachable declaration is visited once. -/
private def closure (env : Environment) (roots : List Name) (localOnly := false) : String := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut entries : List (Name × UInt64) := []
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    if localOnly && !((`SpecTools).isPrefixOf (privateToUserName name)) then continue
    let some info := env.find? name | entries := (name, hash "missing") :: entries; continue
    entries := (name, hash (kindKey info, info.levelParams, info.isUnsafe, info.type,
      info.value? (allowOpaque := true))) :: entries
    pending := info.getUsedConstantsAsSet.toList ++ pending
    if let .recInfo r := info then
      pending := (r.rules.flatMap (fun rule => rule.rhs.getUsedConstants.toList)) ++ pending
  let sorted := entries.mergeSort (fun a b => Name.quickLt a.1 b.1)
  return toString (hash sorted)

def capture (env : Environment) (producer : String) (inputs : Json) (roots : List Name)
    (algorithm : Name := `SpecTools.Evidence.capture) : Fingerprint :=
  ⟨Lean.versionString, producer, toString (hash inputs.compress), closure env roots,
    closure env [algorithm] true⟩

structure Requirement where
  id : String
  clause : String
  declarations : List Name
  deriving FromJson, ToJson

structure Manifest where
  project : String
  requirements : List Requirement
  deriving FromJson, ToJson

structure Context where
  project : String
  snapshot : String
  deriving FromJson, ToJson, DecidableEq

register_option specTools.evidenceManifest : String := {
  defValue := "", descr := "JSON manifest identifying the complete specification shared by related reviews" }

def readManifest : Elab.Command.CommandElabM (Option Manifest) := do
  let path := specTools.evidenceManifest.get (← getOptions)
  if path.isEmpty then return none
  let manifest : Manifest ← ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)
  let ids := manifest.requirements.map (·.id)
  unless !manifest.project.trimAscii.isEmpty && !ids.isEmpty && ids.eraseDups == ids &&
      ids.all (!·.trimAscii.isEmpty) do throwError "Invalid project or requirement IDs in evidence manifest"
  for n in manifest.requirements.flatMap (·.declarations) do
    unless (← getEnv).contains n do throwError "Missing manifest declaration {n}"
  return some manifest

def contextualize (report : Json) (manifest : Option Manifest) : Elab.Command.CommandElabM Json := do
  let some m := manifest | return report
  let deps := closure (← getEnv) (m.requirements.flatMap (·.declarations))
  let ctx : Context := ⟨m.project, toString (hash (Lean.versionString, (toJson m).compress, deps))⟩
  return report.setObjVal! "specification" (toJson ctx)

def attachWith (manifest : Option Manifest) (algorithm : Name) (producer : String) (input : Json)
    (roots : List Name) (report : Json) :
    Elab.Command.CommandElabM Json := do
  contextualize (report.setObjVal! "fingerprint" (toJson (capture (← getEnv) producer input roots algorithm)))
    manifest

def attachReport (algorithm : Name) (producer : String) (input : Json) (roots : List Name) (report : Json) :
    Elab.Command.CommandElabM Json := do
  attachWith (← readManifest) algorithm producer input roots report

/-- Compatibility for standalone producers that supply only a label. -/
def attach (env : Environment) (producer : String) (input : Json) (roots : List Name) (report : Json) : Json :=
  let f := capture env producer input roots
  report.setObjVal! "fingerprint" (Json.mkObj [("producer", toJson f.producer), ("version", toJson f.version),
    ("inputs", toJson f.inputs), ("declarations", toJson f.declarations)])

/-- Bind external requirement wording when the review uses a separate source document. -/
def requirementSource (path : Option System.FilePath) : IO (Option (String × String)) :=
  path.mapM fun p => return (p.toString, ← IO.FS.readFile p)

end SpecTools.Evidence
