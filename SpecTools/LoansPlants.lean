-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Synthetic

/-!
The loans fixture's catalogue of planted gaps, one of each of the eight kinds, as exact-text edits of
`fixtures/loans/`. Each changes what an artifact means and leaves its shape whole: no clause is left
without a theorem or test beside it, and no plant leaves a comment or name that gives it away.
-/

namespace SpecTools.LoansPlants
open SpecTools.Synthetic

def lean (old new : String) : Edit := { file := "Loans.lean", old, new }
def py (old new : String) : Edit := { file := "loans.py", old, new }
def test (old new : String) : Edit := { file := "test_loans.py", old, new }
def prose (old new : String) : Edit := { file := "loans.md", old, new }

def catalogue : List Plant := [
  -- The row names a neighbouring theorem, about standard members, in place of its own.
  { kind := "uncovered", clause := "A premium member who owes any fine may have no more copies on loan than a standard member.", edits := [
      lean "theorem limit_owing (s : State) (m : Nat) (h : 0 < s.fine m) : s.limit m = 5 := by\n  have : s.fine m ≠ 0 := by omega\n  simp [State.limit, this]\n\n" "",
      lean "theorem witness_limit_owing :\n    ∃ (s : State) (m : Nat) (h : 0 < s.fine m), True :=\n  ⟨premiumOwing, 1, by decide, trivial⟩\n\n" "",
      lean "    theorems := [``borrow_at_limit, ``limit_owing],"
        "    theorems := [``borrow_at_limit, ``limit_standard],",
      lean "      ⟨``limit_owing, ``witness_limit_owing, .inhabited⟩] },"
        "      ⟨``limit_standard, ``witness_limit_standard, .inhabited⟩] },"] },
  -- The bound moves by one in the theorem alone.
  { kind := "too weak", clause := "A member may hold at most three copies.", edits := [
      lean "theorem hold_three (s : State) (m c : Nat) (h : 3 ≤ s.holdCount m) : placeHold s m c = none := by\n  simp [placeHold, h]"
        "theorem hold_three (s : State) (m c : Nat) (h : 4 ≤ s.holdCount m) : placeHold s m c = none := by\n  have : 3 ≤ s.holdCount m := by omega\n  simp [placeHold, this]",
      lean "    ∃ (s : State) (m c : Nat) (h : 3 ≤ s.holdCount m), True :=\n  ⟨threeHolds, 2, 10, by decide, trivial⟩"
        "    ∃ (s : State) (m c : Nat) (h : 4 ≤ s.holdCount m), True :=\n  ⟨{ threeHolds with holds := (10, 2) :: threeHolds.holds }, 2, 11, by decide, trivial⟩"] },
  -- A contradictory premise leaves the original witness inapplicable to the new domain.
  { kind := "vacuous", clause := "A member with a loan past its due date may not borrow.", edits := [
      lean "theorem borrow_overdue (s : State) (m c t : Nat) (h : s.overdue m t = true) :\n    borrow s m c t = none := by"
        "theorem borrow_overdue (s : State) (m c t : Nat) (h : s.overdue m t = true)\n    (h' : s.overdue m t = false) : borrow s m c t = none := by"] },
  -- A true statement of behaviour the prose doesn't ask for, with a row of its own.
  { kind := "extra", clause := "Returning a copy keeps its holds.", edits := [
      lean "theorem giveBack_not_on_loan (s : State) (c t : Nat) (h : s.loanOf c = none) : giveBack s c t = s := by\n  simp [giveBack, h]\n"
        "theorem giveBack_not_on_loan (s : State) (c t : Nat) (h : s.loanOf c = none) : giveBack s c t = s := by\n  simp [giveBack, h]\n\ntheorem giveBack_keeps_holds (s : State) (c t : Nat) : (giveBack s c t).holds = s.holds := by\n  unfold giveBack\n  split <;> simp [State.setFine]\n",
      lean "  { id := \"return-unlent\","
        "  { id := \"returns-keep-holds\", clause := \"Returning a copy keeps its holds.\",\n    theorems := [``giveBack_keeps_holds] },\n  { id := \"return-unlent\","] },
  -- The clause leaves the prose; the Lean, the Python and the tests still decide it.
  { kind := "undecided", clause := "A member may not place a hold while their loans and holds together reach their loan limit.", edits := [
      prose "\n\nA member may not place a hold while their loans and holds together reach their loan limit." ""] },
  -- The row's test is renamed, so the name the ledger gives finds nothing.
  { kind := "missing test", clause := "A member who owes 10 or more in fines may not renew.", edits := [
      test "def test_renew_owing(s, m, d, f):  # renew-owing" "def test_renew_owing_check(s, m, d, f):  # renew-owing"] },
  -- The property's second case no longer reaches an overdue loan.
  { kind := "weak test", clause := "A member with a loan past its due date may not borrow.", edits := [
      test "    assert borrow(with_loan(base, Loan(SPARE + 1, m, d)), m, SPARE, d + late) is None"
        "    assert borrow(with_loan(base, Loan(SPARE + 1, m, d + late)), m, SPARE, d) is not None"] },
  -- The cap moves by one everywhere but the prose: model, theorems, Python and tests agree.
  { kind := "shared blind spot", clause := "The fine for one late return is at most 30.", edits := [
      lean "    s'.setFine l.member (s.fine l.member + min 30 (today - l.due))"
        "    s'.setFine l.member (s.fine l.member + min 31 (today - l.due))",
      lean "    (giveBack s c t).fine l.member = s.fine l.member + min 30 (t - l.due) := by"
        "    (giveBack s c t).fine l.member = s.fine l.member + min 31 (t - l.due) := by",
      lean "    (giveBack s c t).fine l.member ≤ s.fine l.member + 30 := by"
        "    (giveBack s c t).fine l.member ≤ s.fine l.member + 31 := by",
      py "FINE_CAP = 30" "FINE_CAP = 31"] }
]

end SpecTools.LoansPlants
