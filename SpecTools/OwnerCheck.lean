import Lean.Data.Json

namespace SpecTools.OwnerCheck

open Lean

inductive Check where
  | audit
  | tests
  | gaps
  | clauses
  deriving DecidableEq

def Check.all : List Check := [.audit, .tests, .gaps, .clauses]

def Check.name : Check → String
  | .audit => "audit"
  | .tests => "tests"
  | .gaps => "gaps"
  | .clauses => "clauses"

private def byName (name : String) : Option Check :=
  if name = "audit" then some .audit
  else if name = "tests" then some .tests
  else if name = "gaps" then some .gaps
  else if name = "clauses" then some .clauses
  else none

def argumentless : Option Json → Bool
  | none => true
  | some (.obj fields) => fields.isEmpty
  | _ => false

/-- Accept a known check with no additional input. -/
def decode (name : String) (arguments : Option Json) : Option Check :=
  if argumentless arguments then byName name else none

private theorem byName_iff (name : String) (check : Check) :
    byName name = some check ↔ name = check.name := by
  unfold byName
  cases check <;> split <;> (try simp_all [Check.name]) <;>
    split <;> (try simp_all) <;> split <;> (try simp_all) <;> split <;> simp_all

private theorem argumentless_iff (arguments : Option Json) :
    argumentless arguments = true ↔
      arguments = none ∨ arguments = some (Json.mkObj []) := by
  cases arguments with
  | none => simp [argumentless]
  | some value =>
    cases value <;> simp [argumentless, Json.mkObj]
    rename_i fields
    have empty : Std.TreeMap.Raw.ofList ([] : List (String × Json)) = ⟨⟨.leaf⟩⟩ := rfl
    rw [empty]
    cases fields with
    | mk fields =>
      cases fields with
      | mk tree =>
        cases tree <;> simp [Std.TreeMap.Raw.isEmpty, Std.DTreeMap.Raw.isEmpty,
          Std.DTreeMap.Internal.Impl.isEmpty]

/-- Exactly the four named, argument-free calls are admitted and each selects its own check. -/
theorem decode_iff (name : String) (arguments : Option Json) (check : Check) :
    decode name arguments = some check ↔
      (arguments = none ∨ arguments = some (Json.mkObj [])) ∧ name = check.name := by
  by_cases accepted : argumentless arguments = true
  · simp [decode, accepted, (argumentless_iff arguments).mp accepted, byName_iff]
  · have h : ¬(arguments = none ∨ arguments = some (Json.mkObj [])) :=
      fun h => accepted ((argumentless_iff arguments).mpr h)
    simp [decode, accepted, h]

/-- The fixed targets available on a generated Lean project. -/
def projectTargets : List (String × String) :=
  [("proofs", "ProofObligations"), ("contracts", "Ledger"), ("counterexamples", "Counterexamples")]

inductive Profile where
  | project
  | pythonLegacy
  deriving DecidableEq

def Profile.names : Profile → List String
  | .project => projectTargets.map Prod.fst
  | .pythonLegacy => ["audit", "integration", "gaps", "clauses"]

def Profile.options : Profile → List String
  | .project => []
  | .pythonLegacy => ["--target", "python"]

/-- Only advertised checks with no caller-controlled arguments are admitted. -/
def admitted (profile : Profile) (name : String) (args : Option Json) : Bool :=
  profile.names.contains name && argumentless args

theorem admitted_iff (profile : Profile) (name : String) (args : Option Json) :
    admitted profile name args = true ↔
      name ∈ profile.names ∧ (args = none ∨ args = some (Json.mkObj [])) := by
  simp [admitted, argumentless_iff]

end SpecTools.OwnerCheck
