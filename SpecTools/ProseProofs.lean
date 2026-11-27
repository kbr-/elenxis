-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Prose

/-!
The fidelity check's comparison: an extraction keeps a document exactly when it gives back the rule
list as a multiset, each rule's measures in any order.
-/

namespace SpecTools.Prose
open SpecTools.Generated

/-- The comparison is equality of the normalized rule lists up to order. -/
theorem faithful_iff (expected got : List Shape) :
    faithful expected got = true ↔ (expected.map Shape.norm).Perm (got.map Shape.norm) := by
  simp [faithful, List.isPerm_iff]

theorem confirmation_exact (expected : List Shape) (first second : Except String (List Shape)) :
    confirmationFaults expected first second = [] ↔
      (∃ actual, first = .ok actual ∧ (expected.map Shape.norm).Perm (actual.map Shape.norm)) ∧
        (∃ actual, second = .ok actual ∧ (expected.map Shape.norm).Perm (actual.map Shape.norm)) := by
  simp only [confirmationFaults_empty_iff, faithful_iff]

private def deliver : Shape := ⟨"deliver", ["requests", "loans"], 15, none⟩

/-- Measures in another order are the same rule. -/
example : faithful [deliver] [⟨"deliver", ["loans", "requests"], 15, none⟩] = true := by
  native_decide
/-- The rules in another order are the same list. -/
example : faithful [deliver, ⟨"pay", ["fines"], 3, some "staff"⟩]
    [⟨"pay", ["fines"], 3, some "staff"⟩, deliver] = true := by native_decide
/-- A wrong bound, a dropped exception, a missing rule, a rule given twice and one added each
discard the document. -/
example : faithful [deliver] [{ deliver with bound := 16 }] = false := by native_decide
example : faithful [{ deliver with flag := some "staff" }] [deliver] = false := by native_decide
example : faithful [deliver, ⟨"pay", ["fines"], 3, none⟩] [deliver] = false := by native_decide
example : faithful [deliver] [deliver, deliver] = false := by native_decide
example : faithful [deliver] [deliver, ⟨"pay", ["fines"], 3, none⟩] = false := by native_decide

/-- An extraction answer is read in the generator's terms, `none` for no exemption. -/
example : shapesOf (Lean.Json.mkObj [("rules", Lean.Json.arr #[Lean.Json.mkObj [
    ("kind", "deliver"), ("measures", Lean.Json.arr #["requests", "loans"]), ("bound", 15),
    ("exempt", "none")]])]) = some [deliver.norm] := by native_decide

/-- A saved rule reads back as it was, with and without an exemption. -/
example : ruleOfJson (ruleJson ⟨4, "pay", ["fines", "debts"], 7, some "staff"⟩) =
    some ⟨4, "pay", ["fines", "debts"], 7, some "staff"⟩ := by native_decide
example : ruleOfJson (ruleJson ⟨0, "deliver", ["loans"], 2, none⟩) =
    some ⟨0, "deliver", ["loans"], 2, none⟩ := by native_decide

/-- Folded rules pair in order. -/
example : foldPairs [(0, .folded), (1, .plain), (2, .folded), (3, .folded), (4, .folded)] =
    [(0, 2), (3, 4)] := by native_decide

end SpecTools.Prose
