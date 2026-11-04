import SpecTools.Synthetic

/-!
The loans fixture's catalogue of planted gaps, one of each of the eight kinds, as exact-text edits of
`fixtures/loans/`. A plant leaves no comment or name that gives it away.
-/

namespace SpecTools.LoansPlants
open SpecTools.Synthetic

def lean (old new : String) : Edit := { file := "Loans.lean", old, new }
def py (old new : String) : Edit := { file := "loans.py", old, new }
def test (old new : String) : Edit := { file := "test_loans.py", old, new }
def prose (old new : String) : Edit := { file := "loans.md", old, new }

def catalogue : List Plant := [
  { kind := "uncovered", clause := "A copy has at most one hold.", edits := [
      lean "theorem hold_one (s : State) (m c : Nat) (h : s.holds.any (·.1 == c) = true) : placeHold s m c = none := by\n  simp [placeHold, h]\n\n" "",
      lean "theorem witness_one_hold : heldLent.holds.any (·.1 == 7) = true := by decide\n" "",
      lean "  { id := \"one-hold\", clause := \"A copy has at most one hold.\",\n    theorems := [``hold_one], witnesses := [``witness_one_hold] },\n" ""] },
  { kind := "too weak", clause := "Paying reduces a member's fines by the amount paid, and never below zero.", edits := [
      lean "theorem pay_reduces (s : State) (m a : Nat) : (pay s m a).fine m = s.fine m - a := by"
        "theorem pay_reduces (s : State) (m a : Nat) : (pay s m a).fine m ≤ s.fine m := by"] },
  { kind := "vacuous", clause := "A member who owes 10 or more in fines may not borrow.", edits := [
      lean "theorem borrow_owing (s : State) (m c t : Nat) (h : 10 ≤ s.fine m) : borrow s m c t = none := by"
        "theorem borrow_owing (s : State) (m c t : Nat) (h : 10 ≤ s.fine m) (h' : s.fine m < 10) : borrow s m c t = none := by",
      lean "theorem witness_owing : 10 ≤ heldLent.fine 3 := by decide\n" "",
      lean "    theorems := [``borrow_owing], witnesses := [``witness_owing] },"
        "    theorems := [``borrow_owing] },"] },
  { kind := "extra", clause := "Paying the whole fine clears it.", edits := [
      lean "theorem refused_changes_nothing (s : State) : apply s none = s := rfl\n"
        "theorem refused_changes_nothing (s : State) : apply s none = s := rfl\n\ntheorem pay_all (s : State) (m : Nat) : (pay s m (s.fine m)).fine m = 0 := by\n  simp [pay, State.setFine, State.fine]\n",
      lean "  { id := \"refusal\", clause := \"A request that is refused changes nothing.\","
        "  { id := \"pay-all\", clause := \"Paying the whole fine clears it.\", theorems := [``pay_all] },\n  { id := \"refusal\", clause := \"A request that is refused changes nothing.\","] },
  { kind := "undecided", clause := "A copy that is not on loan can't be held.", edits := [
      prose "A copy that is not on loan can't be held.\n\n" ""] },
  { kind := "missing test", clause := "A loan cannot be renewed after its due date.", edits := [
      test "@given(STATES, MEMBERS, DAYS, st.integers(1, 30))\ndef test_renew_late(s, m, d, late):  # renew-late\n    assert renew(with_loan(s, Loan(SPARE, m, d)), m, SPARE, d + late) is None\n\n\n" ""] },
  { kind := "weak test", clause := "A copy that another member holds may not be borrowed.", edits := [
      test "    held = replace(s, holds=((c, other(m)),) + s.holds)\n    assert borrow(held, m, c, t) is None\n"
        "    held = replace(s, holds=((c, other(m)),) + s.holds)\n    result = borrow(held, m, c, t)\n    assert result is None or result.count(m) <= MAX_LOANS\n"] },
  { kind := "shared blind spot", clause := "A member may not hold a copy they have on loan.", edits := [
      lean "theorem hold_own (s : State) (m c : Nat) (h : s.loans.any (fun l => l.copy == c && l.member == m) = true) :\n    placeHold s m c = none := by\n  simp [placeHold, h]\n\n" "",
      lean "theorem witness_own : lent.loans.any (fun l => l.copy == 7 && l.member == 1) = true := by decide\n" "",
      lean "  { id := \"hold-own\", clause := \"A member may not hold a copy they have on loan.\",\n    theorems := [``hold_own], witnesses := [``witness_own] },\n" "",
      test "@given(STATES, MEMBERS)\ndef test_hold_own(s, m):  # hold-own\n    assert place_hold(with_loan(s, Loan(SPARE, m, 14)), m, SPARE) is None\n\n\n" "",
      py "    if (not state.on_loan(copy) or any(x.copy == copy and x.member == member for x in state.loans)\n            or any(c == copy for c, _ in state.holds)):"
        "    if (not state.on_loan(copy)\n            or any(c == copy for c, _ in state.holds)):"] }
]

end SpecTools.LoansPlants
