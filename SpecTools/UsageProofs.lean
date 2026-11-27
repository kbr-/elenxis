-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Usage

/-!
The usage record's laws: the empty record is the unit of the total, totals combine associatively
(so a batch's total is its variants' totals added), and a total of single calls counts exactly the
calls that lacked a field, beside the sum of those that reported it.
-/

namespace SpecTools.Usage

@[simp] theorem field_add_known (a b : Field) : (a + b).known = a.known + b.known := rfl
@[simp] theorem field_add_lacking (a b : Field) : (a + b).lacking = a.lacking + b.lacking := rfl

theorem Field.ext' {a b : Field} (h1 : a.known = b.known) (h2 : a.lacking = b.lacking) : a = b := by
  cases a; cases b; simp_all

theorem field_zero_add (a : Field) : ({} : Field) + a = a := Field.ext' (by simp) (by simp)
theorem field_add_zero (a : Field) : a + ({} : Field) = a := Field.ext' (by simp) (by simp)
theorem field_add_assoc (a b c : Field) : a + b + c = a + (b + c) :=
  Field.ext' (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])

theorem zero_add (a : Usage) : ({} : Usage) + a = a := by
  cases a; simp only [HAdd.hAdd, Add.add]; simp

theorem add_zero (a : Usage) : a + ({} : Usage) = a := by
  cases a; simp only [HAdd.hAdd, Add.add]; simp

theorem add_assoc (a b c : Usage) : a + b + c = a + (b + c) := by
  cases a; cases b; cases c; simp only [HAdd.hAdd, Add.add]; simp [Nat.add_assoc]

@[simp] theorem total_nil : total [] = {} := rfl

/-- A batch's total is its parts' totals added. -/
theorem total_append (xs ys : List Usage) : total (xs ++ ys) = total xs + total ys := by
  induction xs with
  | nil => simp [total, zero_add]
  | cons x xs ih => simp only [List.cons_append, total, List.foldr_cons] at *; rw [ih, add_assoc]

/-- A total of single calls' counts: the sum of the reported ones, and the number that lacked it.
A reader turning a lacking count into 0 breaks the second half: its total would claim no call
lacked the field. -/
theorem field_total (xs : List (Option Nat)) :
    (xs.map Field.of).foldr (· + ·) ({} : Field) =
      { known := (xs.filterMap id).sum, lacking := (xs.filter (·.isNone)).length } := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    cases x <;> apply Field.ext' <;> simp [Field.of] <;> omega

/-- A call no harness reported on adds one to every count's lacking calls, and nothing known. -/
theorem unreported_lacking (u : Usage) (ms : Nat) :
    (u + unreported ms).input = { known := u.input.known, lacking := u.input.lacking + 1 } ∧
    (u + unreported ms).output = { known := u.output.known, lacking := u.output.lacking + 1 } := by
  constructor <;> rfl

/-- The price Claude Code printed for the probe question, `0.018001800000000002`, in billionths. -/
example : nanoOf ⟨18001800000000002, 18⟩ = some 18001800 := by decide

end SpecTools.Usage
