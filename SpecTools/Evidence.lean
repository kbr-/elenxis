-- SPDX-License-Identifier: Apache-2.0
import Lean

namespace SpecTools.Evidence
open Lean

structure Fingerprint where
  version : String
  producer : String
  inputs : String
  declarations : String
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
def capture (env : Environment) (producer : String) (inputs : Json) (roots : List Name) : Fingerprint := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut entries : List (Name × UInt64) := []
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | entries := (name, hash "missing") :: entries; continue
    entries := (name, hash (kindKey info, info.levelParams, info.isUnsafe, info.type,
      info.value? (allowOpaque := true))) :: entries
    pending := info.getUsedConstantsAsSet.toList ++ pending
    if let .recInfo r := info then
      pending := (r.rules.flatMap (fun rule => rule.rhs.getUsedConstants.toList)) ++ pending
  let sorted := entries.mergeSort (fun a b => Name.quickLt a.1 b.1)
  return ⟨Lean.versionString, producer, toString (hash inputs.compress), toString (hash sorted)⟩

def attach (env : Environment) (producer : String) (input : Json) (roots : List Name) (report : Json) : Json :=
  report.setObjVal! "fingerprint" (toJson (capture env producer input roots))

/-- Bind external requirement wording when the review uses a separate source document. -/
def requirementSource (path : Option System.FilePath) : IO (Option (String × String)) :=
  path.mapM fun p => return (p.toString, ← IO.FS.readFile p)

end SpecTools.Evidence
