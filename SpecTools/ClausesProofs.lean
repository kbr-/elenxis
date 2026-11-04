import SpecTools.Clauses

/-!
The comparison of two extractions: equal ones differ in nothing; extractions differing in one
clause differ in that clause, once; and a reported clause is one that one side has and the other
lacks.
-/

namespace SpecTools.Clauses

theorem missingFrom_nil {a b : List String} (h : ∀ x ∈ b, x ∈ a) : missingFrom a b = [] := by
  have : b.filter (fun x => !a.contains x) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; simp [h x hx]
  simp only [missingFrom, this]
  rfl

theorem missingFrom_self (a : List String) : missingFrom a a = [] :=
  missingFrom_nil fun _ hx => hx

/-- Equal extractions print nothing. -/
theorem differences_self (a : List String) : differences a a = [] := by
  simp [differences, missingFrom_self]

/-- A clause is reported exactly when one extraction has it and the other doesn't. -/
theorem mem_differences (a b : List String) (c : String) :
    c ∈ differences a b ↔ (c ∈ b ∧ c ∉ a) ∨ (c ∈ a ∧ c ∉ b) := by
  simp [differences, missingFrom, List.mem_eraseDups]

/-- Extractions differing in one clause print that clause, once. -/
theorem differences_one (a : List String) (c : String) (h : c ∉ a) :
    differences a (a ++ [c]) = [c] := by
  have h1 : missingFrom a (a ++ [c]) = [c] := by
    simp only [missingFrom, List.filter_append]
    have : a.filter (fun x => !a.contains x) = [] := by
      simp [List.filter_eq_nil_iff]
    rw [this]
    simp [h]
    rfl
  have h2 : missingFrom (a ++ [c]) a = [] := missingFrom_nil fun x hx => by simp [hx]
  simp [differences, h1, h2]

/-- A witness for `differences_one`'s hypothesis. -/
example : "a hold blocks renewal" ∉ ["a loan ends by its due date"] := by decide

end SpecTools.Clauses
