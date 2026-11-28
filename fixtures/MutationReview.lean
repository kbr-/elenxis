-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Mutation

namespace MutationReview
open SpecTools.Mutation SpecTools.Score.Evidence

def both (n : Nat) : Prop := n < 10 ∧ n ≠ 0
def belowTen (n : Nat) : Prop := n < 10
def zero : Nat := 0
def ten : Nat := 10
def nine : Nat := 9
def atMost (n : Nat) := n ≤ 10
def equalTen (n : Nat) := n = 10
def unequalTen (n : Nat) := n ≠ 10
def allEqual (n : Nat) := ∀ k : Nat, k = n
def someEqual (n : Nat) := ∃ k : Nat, k = n
theorem upper : Distinguishes belowTen atMost .admitsExtra ten := by
  simp [Distinguishes, belowTen, atMost, ten]
theorem stricter : Distinguishes atMost belowTen .rejectsRequired ten := by
  simp [Distinguishes, atMost, belowTen, ten]
theorem raised : Distinguishes belowTen (fun n => n < 11) .admitsExtra ten := by
  simp [Distinguishes, belowTen, ten]
theorem lowered : Distinguishes belowTen (fun n => n < 9) .rejectsRequired nine := by
  simp [Distinguishes, belowTen, nine]
theorem unequal : Distinguishes equalTen unequalTen .rejectsRequired ten := by
  simp [Distinguishes, equalTen, unequalTen, ten]
theorem equal : Distinguishes unequalTen equalTen .admitsExtra ten := by
  simp [Distinguishes, equalTen, unequalTen, ten]
theorem notAll : ¬ allEqual zero := fun h => Nat.one_ne_zero (h 1)
theorem anyAtZero : someEqual zero := ⟨0, rfl⟩
theorem existsExtra : Distinguishes allEqual someEqual .admitsExtra zero := ⟨anyAtZero, notAll⟩
theorem forallMissing : Distinguishes someEqual allEqual .rejectsRequired zero := ⟨anyAtZero, notAll⟩

theorem weaker : Relation.strictlyWeaker.Holds both belowTen :=
  ⟨fun _ h => h.1, ⟨0, (by decide : 0 < 10), fun h => h.2 rfl⟩⟩
theorem extra : Distinguishes both belowTen .admitsExtra zero :=
  ⟨(by decide : 0 < 10), fun h => h.2 rfl⟩

def guarded (n : Nat) : Prop := n = 0 → n < 10
def reversed (n : Nat) : Prop := n < 10 → n = 0
def nonzero (n : Nat) : Prop := n ≠ 0

theorem remaining (n : Nat) : both n → nonzero n := And.right
theorem guardedTotal (n : Nat) : guarded n := by intro h; subst n; decide
theorem reversedStronger : Relation.strictlyStronger.Holds guarded reversed := by
  refine ⟨fun n _ => guardedTotal n, 1, guardedTotal 1, ?_⟩
  intro h
  exact Nat.one_ne_zero (h (by decide))
theorem unguardedImplies (n : Nat) : belowTen n → guarded n := fun h _ => h
theorem totalEquivalent (n : Nat) : guarded n ↔ True := ⟨fun _ => trivial, fun _ => guardedTotal n⟩
theorem emptyDisjoint : ¬ ∃ n : Nat, both n ∧ False := fun ⟨_, _, h⟩ => h

abbrev Sorter := List Nat → List Nat
def emptyOutput : Sorter := fun _ => []
def sorted (sort : Sorter) : Prop := ∀ xs, (sort xs).Pairwise (· ≤ ·)
def preservesLength (sort : Sorter) : Prop := ∀ xs, (sort xs).length = xs.length
theorem sortedEmpty : sorted emptyOutput := fun _ => List.Pairwise.nil
theorem losesElement : ¬ preservesLength emptyOutput := fun h => by have := h [0]; contradiction
def preservesEmptyLength (sort : Sorter) : Prop := (sort []).length = 0
theorem emptyLength : preservesEmptyLength emptyOutput := rfl

universe u
def hasElement (α : Type u) : Prop := Nonempty α
theorem allUniverses : Relation.equivalent.Holds hasElement.{u} hasElement.{u} := fun _ => Iff.rfl
theorem onlySmallTypes : Relation.equivalent.Holds hasElement.{0} hasElement.{0} := fun _ => Iff.rfl

def base : Candidate := {
  id := "drop-nonzero", requirement := "number in range", revision := "fixture-v1",
  origin := "deterministic", original := ``both, candidate := .dropRightConjunct,
  attempts := [⟨.relation .strictlyWeaker, some ``weaker⟩, ⟨.distinguishes .admitsExtra ``zero, some ``extra⟩],
  scenario := "Zero meets the upper bound.", proposedProperty := "State whether zero is permitted." }

open Lean Elab Command in
run_cmd do
  let cases := [base,
    { base with id := "wrong-proof", attempts := [⟨.relation .equivalent, some ``weaker⟩] },
    { base with id := "no-proof", attempts := [⟨.relation .equivalent, none⟩] },
    { base with id := "bad-shape", candidate := .reverseImplication },
    { base with id := "not-run", attempts := [] },
    { base with
      id := "empty-sorted", requirement := "sort order", original := ``sorted,
      candidate := .named ``emptyOutput, attempts := [⟨.satisfies, some ``sortedEmpty⟩] },
    { base with
      id := "empty-length", requirement := "sort length", original := ``preservesLength,
      candidate := .named ``emptyOutput,
      attempts := [⟨.refutes, some ``losesElement⟩, ⟨.satisfies, some ``emptyLength⟩] },
    { id := "one-input", requirement := "sort length on empty input", revision := "fixture-v1",
      origin := "named model", original := ``preservesEmptyLength, candidate := .named ``emptyOutput,
      attempts := [⟨.satisfies, some ``emptyLength⟩] },
    { id := "universe-scope", requirement := "type inhabitation", revision := "fixture-v1",
      origin := "universe scope control", original := ``hasElement, candidate := .named ``hasElement,
      attempts := [⟨.relation .equivalent, some ``allUniverses⟩,
        ⟨.relation .equivalent, some ``onlySmallTypes⟩] }]
  let scheduled : ScheduledCheck := ⟨base.requirement, base.revision, base.id, base.original,
    base.candidate, .relation .strictlyWeaker⟩
  let absent := [{ scheduled with id := "not-submitted" }, { scheduled with revision := "other" },
    { scheduled with challenge := .refutes }, { scheduled with candidate := .alwaysFalse }]
  let report ← review cases (some (scheduled :: absent))
  unless (report.getObjVal? "missingScheduledChecks").toOption == some (toJson absent) do
    throwError "schedule mismatch: {report}"
  let candidates : Array Json ← Lean.ofExcept (report.getObjValAs? (Array Json) "candidates")
  let outcomes ← candidates.mapM fun (c : Json) => do
    let checks : Array Json ← Lean.ofExcept (c.getObjValAs? (Array Json) "checks")
    checks.mapM fun (check : Json) => Lean.ofExcept (check.getObjValAs? String "status")
  unless outcomes == #[#["established", "established"], #["inconclusive"], #["inconclusive"],
      #["invalid", "invalid"], #[], #["established"], #["established", "inconclusive"],
      #["established"], #["established", "inconclusive"]] do
    throwError "unexpected mutation results: {report}"
  unless (candidates[4]!.getObjValAs? Bool "attempted").toOption == some false do
    throwError "unattempted candidate lost"
  let operators := [
    { base with id := "left", candidate := .dropLeftConjunct, attempts := [⟨.relation .implies, some ``remaining⟩] },
    { base with
      id := "reverse", original := ``guarded, candidate := .reverseImplication,
      attempts := [⟨.relation .strictlyStronger, some ``reversedStronger⟩] },
    { base with
      id := "drop-pre", original := ``guarded, candidate := .dropPrecondition,
      attempts := [⟨.relation .refines, some ``unguardedImplies⟩] },
    { base with
      id := "true", original := ``guarded, candidate := .alwaysTrue,
      attempts := [⟨.relation .equivalent, some ``totalEquivalent⟩] },
    { base with id := "false", candidate := .alwaysFalse, attempts := [⟨.relation .incompatible, some ``emptyDisjoint⟩] }]
  let boundary (id : String) (orig : Lean.Name) (op : Variant) (dir : Direction)
      (obs cert : Lean.Name) : Candidate :=
    { base with id, original := orig, candidate := op, attempts := [⟨.distinguishes dir obs, some cert⟩] }
  let generated ← review (operators ++ [
    boundary "strict" ``belowTen .toggleStrictness .admitsExtra ``ten ``upper,
    boundary "nonstrict" ``atMost .toggleStrictness .rejectsRequired ``ten ``stricter,
    boundary "increment" ``belowTen .raiseNatBoundary .admitsExtra ``ten ``raised,
    boundary "decrement" ``belowTen .lowerNatBoundary .rejectsRequired ``nine ``lowered,
    boundary "disequality" ``equalTen .toggleEquality .rejectsRequired ``ten ``unequal,
    boundary "equality" ``unequalTen .toggleEquality .admitsExtra ``ten ``equal,
    boundary "negate" ``equalTen .negatePredicate .rejectsRequired ``ten ``unequal,
    boundary "exists" ``allEqual .toggleQuantifier .admitsExtra ``zero ``existsExtra,
    boundary "forall" ``someEqual .toggleQuantifier .rejectsRequired ``zero ``forallMissing])
  let results : Array Json ← Lean.ofExcept (generated.getObjValAs? (Array Json) "candidates")
  for r in results do
    let check ← Lean.ofExcept (r.getObjVal? "checks" >>= (·.getArrVal? 0))
    unless (check.getObjValAs? String "status").toOption == some "established" do
      throwError "operator failed: {r}"
  IO.println report.compress

end MutationReview
