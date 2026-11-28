-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Audit

namespace DomainAudit
open SpecTools.Ledger

def Fiber : Bool → Type
  | false => Unit
  | true => Empty

theorem behavior (b : Bool) (_ : Fiber b) : True := trivial
theorem feasible : ∃ b : Bool, ∃ _ : Fiber b, True := ⟨false, (), trivial⟩
theorem notUniform : ¬ (∀ b : Bool, ∃ _ : Fiber b, True) := by
  intro h
  obtain ⟨x, _⟩ := h true
  exact nomatch x

theorem impossible (x : Empty) : False := nomatch x
theorem noInput : ¬ (∃ _ : Empty, True) := by
  rintro ⟨x, _⟩
  exact nomatch x

theorem noContextBehavior (x : Empty) (_ : Nat) : False := nomatch x
theorem vacuousUniform (x : Empty) : ∃ _ : Nat, True := nomatch x
def nestedObligation : Prop := ∀ n : Nat, ∃ m, m > n

theorem guarded (n : Nat) (h : n < 0) : False := by omega
theorem joint (n : Nat) (_ : n = 0) (_ : n = 1) : True := trivial
theorem noJoint : ¬ (∃ n : Nat, ∃ _ : n = 0, ∃ _ : n = 1, True) := by
  rintro ⟨_, rfl, h, _⟩
  contradiction
theorem nested (_ : { n : Nat // n < 0 }) : ∀ b : Bool, b = b := by simp
theorem noSubtype : ¬ (∃ _ : { n : Nat // n < 0 }, True) := by
  rintro ⟨⟨_, h⟩, _⟩
  omega

def row (id : String) (name : Lean.Name) (scope : DomainScope)
    (supports refutes : List Lean.Name := []) : Row :=
  { id, clause := id, theorems := [name], applicability := [⟨name, scope, supports, refutes⟩] }

def rows := [
  row "global" ``behavior (.someInput 2) [``feasible],
  row "uniform" ``behavior (.eachContext 1 1) [``feasible] [``notUniform],
  row "wrong" ``behavior (.eachContext 1 1) [``feasible],
  row "missing" ``impossible (.someInput 1),
  row "empty" ``impossible (.someInput 1) [] [``noInput],
  row "exclusion" ``guarded .exclusion,
  row "joint" ``joint (.someInput 3) [] [``noJoint],
  row "subtype" ``nested (.someInput 1) [] [``noSubtype],
  row "no-context-uniform" ``noContextBehavior (.eachContext 1 1) [``vacuousUniform],
  row "no-context-exists" ``noContextBehavior (.someInput 1) [] [``noInput],
  row "nested-intent" ``nested (.unsupported ``nestedObligation),
  { id := "legacy", clause := "impossibility", theorems := [``impossible],
    status := .accepted "recorded in ledger" }]

#eval SpecTools.Audit.run rows `DomainAudit (emitEvidence := true)

open Lean Elab Command in
run_cmd
  let (facts, checked) ← SpecTools.Audit.inspectRows rows true
  let issues ← SpecTools.Audit.rowAuditIssues true facts rows checked
  let expected := ["uniform", "wrong", "missing", "empty", "joint", "subtype",
    "no-context-exists", "nested-intent"]
  unless issues.length == expected.length && expected.all (fun id =>
      issues.any (·.startsWith s!"applicability {id} ")) do
    throwError "unexpected strict audit issues: {issues}"

end DomainAudit
