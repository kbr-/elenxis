-- SPDX-License-Identifier: Apache-2.0
import Lean.Meta.AppBuilder
import Lean.Data.Json

namespace SpecTools.FiniteGaps
open Lean

structure Request where
  kind : String
  counts : List (String × Nat)
  deriving DecidableEq, ToJson

def Request.get (q : Request) (field : String) : Nat := (q.counts.lookup field).getD 0

/-- An executable condition for a generated refusal statement. -/
structure Scope where
  kind : String
  measures : List String
  bound : Nat
  exempt : Option String := none
  below : Option (String × Nat) := none
  deriving DecidableEq, Repr

def Scope.holds (s : Scope) (q : Request) : Bool :=
  q.kind == s.kind &&
    decide (s.bound ≤ (s.measures.map q.get).sum) &&
    s.exempt.all (fun field => q.get field == 0) &&
    s.below.all (fun (field, cut) => q.get field < cut)

def Scope.sameCondition (left right : Scope) : Bool :=
  decide (left.kind = right.kind ∧ left.bound = right.bound ∧ left.exempt = right.exempt ∧
    left.below = right.below ∧ left.measures.Perm right.measures)

theorem sameCondition_iff (left right : Scope) :
    left.sameCondition right = true ↔
      left.kind = right.kind ∧ left.bound = right.bound ∧ left.exempt = right.exempt ∧
        left.below = right.below ∧ left.measures.Perm right.measures := by
  simp [Scope.sameCondition]

theorem sameCondition_holds (left right : Scope) (request : Request)
    (condition : left.sameCondition right = true) :
    left.holds request = right.holds request := by
  have ⟨kind, bound, exempt, below, measures⟩ := of_decide_eq_true condition
  simp only [Scope.holds, kind, bound, exempt, below, (measures.map request.get).sum_nat]

def Scope.fields (s : Scope) : List String :=
  s.measures ++ s.exempt.toList ++ s.below.toList.map Prod.fst

def Scope.cutoff (s : Scope) : Nat :=
  max 1 (max s.bound ((s.below.map Prod.snd).getD 0))

inductive Difference where
  | missingRefusal
  | extraRefusal
  deriving DecidableEq, Repr

def compareAt (requirement statement : Scope) (request : Request) : Option Difference :=
  match requirement.holds request, statement.holds request with
  | true, false => some .missingRefusal
  | false, true => some .extraRefusal
  | _, _ => none

theorem missing_refusal (requirement statement : Scope) (request : Request) :
    compareAt requirement statement request = some .missingRefusal ↔
      requirement.holds request = true ∧ statement.holds request = false := by
  unfold compareAt
  cases requirement.holds request <;> cases statement.holds request <;> simp

theorem extra_refusal (requirement statement : Scope) (request : Request) :
    compareAt requirement statement request = some .extraRefusal ↔
      requirement.holds request = false ∧ statement.holds request = true := by
  unfold compareAt
  cases requirement.holds request <;> cases statement.holds request <;> simp

theorem compareAt_eq_none_iff (requirement statement : Scope) (request : Request) :
    compareAt requirement statement request = none ↔
      requirement.holds request = statement.holds request := by
  unfold compareAt
  cases requirement.holds request <;> cases statement.holds request <;> simp

theorem exempt_request (scope : Scope) (request : Request) (field : String)
    (exemption : scope.exempt = some field) (present : 0 < request.get field) :
    scope.holds request = false := by
  have nonzero : request.get field ≠ 0 := Nat.ne_of_gt present
  simp [Scope.holds, exemption, nonzero]

/-- The finite assignments for the requested fields. Flags alone distinguish zero from nonzero. -/
def assignments (bound : Nat) (numeric : List String) :
    List String → List (List (String × Nat))
  | [] => [[]]
  | field :: fields =>
    let tail := assignments bound numeric fields
    let top := if numeric.contains field then bound else 1
    (List.range (top + 1)).flatMap fun value => tail.map ((field, value) :: ·)

def requests (requirement statement : Scope) : List Request :=
  let numeric := requirement.measures ++ statement.measures ++
    requirement.below.toList.map Prod.fst ++ statement.below.toList.map Prod.fst
  let fields := (requirement.fields ++ statement.fields).eraseDups
  let cap := max requirement.cutoff statement.cutoff
  let counts := assignments cap numeric fields
  ([requirement.kind, statement.kind].eraseDups).flatMap fun kind => counts.map (Request.mk kind)

/-- A concrete witness records how the predicates differ and where they differ. -/
def findDifference (requirement statement : Scope) : Option (Difference × Request) :=
  (requests requirement statement).findSome? fun request =>
    (compareAt requirement statement request).map (·, request)

/-- Exhaustion establishes agreement on precisely the enumerated search domain. -/
theorem search_none_iff (requirement statement : Scope) :
    findDifference requirement statement = none ↔
      ∀ request ∈ requests requirement statement,
        requirement.holds request = statement.holds request := by
  simp only [findDifference, List.findSome?_eq_none_iff, Option.map_eq_none_iff,
    compareAt_eq_none_iff]

theorem search_sameCondition (requirement statement : Scope)
    (condition : requirement.sameCondition statement = true) :
    findDifference requirement statement = none :=
  (search_none_iff requirement statement).mpr fun request _ =>
    sameCondition_holds requirement statement request condition

theorem search_sound (requirement statement : Scope) (direction : Difference) (request : Request)
    (h : findDifference requirement statement = some (direction, request)) :
    compareAt requirement statement request = some direction := by
  unfold findDifference at h
  generalize requests requirement statement = candidates at h
  induction candidates with
  | nil => simp [List.findSome?] at h
  | cons candidate tail ih =>
    cases found : compareAt requirement statement candidate with
    | none => exact ih (by simpa [List.findSome?, found] using h)
    | some difference =>
      have heq : difference = direction ∧ candidate = request := by
        simpa [List.findSome?, found] using h
      rcases heq with ⟨rfl, rfl⟩
      exact found

private def arguments (name : Name) (count : Nat) (e : Expr) : Option (Array Expr) :=
  let args := e.getAppArgs
  if e.getAppFn.isConstOf name && args.size == count then some args else none

private def stringLiteral : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

private def natLiteral (e : Expr) : Option Nat := do
  let value ← if let .lit (.natVal _) := e then some e else do
    let args ← arguments ``OfNat.ofNat 3 e
    guard (args[0]!.isConstOf ``Nat)
    guard (args[2]! == mkApp (mkConst ``instOfNatNat) args[1]!)
    args[1]?
  match value with
  | .lit (.natVal n) => some n
  | _ => none

private def field (q e : Expr) : Option String := do
  let args ← arguments `Loans.Req.get 2 e
  guard (args[0]! == q)
  stringLiteral args[1]!

private def sumFields (q : Expr) : Expr → Option (List String)
  | e@(.app (.app op left) right) =>
    match field q e with
    | some f => some [f]
    | none => do
      let args ← arguments ``HAdd.hAdd 4 op
      guard ((args.extract 0 3).all (·.isConstOf ``Nat))
      let addition ← arguments ``instHAdd 2 args[3]!
      guard (addition[0]!.isConstOf ``Nat && addition[1]!.isConstOf ``instAddNat)
      return (← sumFields q left) ++ (← sumFields q right)
  | _ => none

private def kindPremise (q h : Expr) : Option String := do
  let args ← arguments ``Eq 3 h
  guard (args[0]!.isConstOf ``String)
  let base ← arguments `Loans.Req.kind 1 args[1]!
  guard (base[0]! == q)
  stringLiteral args[2]!

private def boundPremise (q h : Expr) : Option (Nat × List String) := do
  let args ← arguments ``LE.le 4 h
  guard (args[0]!.isConstOf ``Nat && args[1]!.isConstOf `instLENat)
  return (← natLiteral args[2]!, ← sumFields q args[3]!)

private def flagPremise (q h : Expr) : Option String := do
  let args ← arguments ``Eq 3 h
  guard (args[0]!.isConstOf ``Nat && natLiteral args[2]! == some 0)
  field q args[1]!

private def belowPremise (q h : Expr) : Option (String × Nat) := do
  let args ← arguments ``LT.lt 4 h
  guard (args[0]!.isConstOf ``Nat && args[1]!.isConstOf `instLTNat)
  return (← field q args[2]!, ← natLiteral args[3]!)

private def qualifiers (q : Expr) :
    List Expr → Option (Option String × Option (String × Nat))
  | [] => some (none, none)
  | [h] => (flagPremise q h).map (some ·, none) <|>
      (belowPremise q h).map (none, some ·)
  | [h, k] => do return (some (← flagPremise q h), some (← belowPremise q k))
  | _ => none

/-- Read every premise of a supported synthetic theorem and name the rule in its conclusion. -/
def statementScope (name : Name) : MetaM (Option (Name × Scope)) := do
  let some info := (← getEnv).find? name | return none
  Meta.forallTelescope info.type fun binders conclusion => do
    let domain ← binders.toList.mapM Meta.inferType
    return do
      let q :: _ := binders.toList | none
      let req :: kindHyp :: boundHyp :: rest := domain | none
      guard (req.isConstOf `Loans.Req)
      let args ← arguments ``Eq 3 conclusion
      guard (args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true)
      let fires ← arguments `Loans.fires 2 args[1]!
      guard (fires[1]! == q)
      let .const rule _ := fires[0]! | none
      let kind ← kindPremise q kindHyp
      let (bound, measures) ← boundPremise q boundHyp
      let (exempt, below) ← qualifiers q rest
      return (rule, ⟨kind, measures, bound, exempt, below⟩)

/-- Check the request accessor before interpreting a theorem's premises as field lookups. -/
def requestAccessMatches : MetaM Bool := do
  let some accessor := (← getEnv).find? `Loans.Req.get | return false
  Meta.forallTelescope accessor.type fun args _ => do
    let #[q, fieldName] := args | return false
    let request := mkApp2 (mkConst ``Request.mk)
      (mkApp (mkConst `Loans.Req.kind) q) (mkApp (mkConst `Loans.Req.vals) q)
    Meta.isDefEq (mkApp2 (mkConst accessor.name) q fieldName)
      (mkApp2 (mkConst ``Request.get) request fieldName)

/-- Verify actual membership and the rule-to-refusal theorem's interface in the current fixture. -/
def establishesRefusal (rule : Name) : MetaM Bool := do
  let some proof := (← getEnv).find? `Loans.refused_of | return false
  let rules := mkConst `Loans.rules
  let member ← Meta.mkAppM ``Membership.mem #[rules, mkConst rule]
  let listMember ← Meta.mkAppM ``List.Mem #[mkConst rule, rules]
  unless ← Meta.isDefEq member listMember do return false
  let .some instanceTerm ← Meta.trySynthInstance (mkApp (mkConst ``Decidable) member) |
    return false
  let actual := mkApp2 (mkConst ``decide) member instanceTerm
  unless ← Meta.withTransparency .all (Meta.isDefEq actual (mkConst ``Bool.true)) do
    return false
  Meta.forallTelescope proof.type fun args conclusion => do
    let #[r, q, inRules, fires] := args | return false
    let memType ← Meta.mkAppM ``List.Mem #[r, rules]
    let firesType ← Meta.mkEq (mkApp2 (mkConst `Loans.fires) r q) (mkConst ``Bool.true)
    let refusal ← Meta.mkEq (mkApp (mkConst `Loans.refused) q) (mkConst ``Bool.true)
    return (← Meta.isDefEq (← Meta.inferType inRules) memType) &&
      (← Meta.isDefEq (← Meta.inferType fires) firesType) &&
      (← Meta.isDefEq conclusion refusal)

end SpecTools.FiniteGaps
