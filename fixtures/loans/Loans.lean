import SpecTools.Audit

/-!
The synthetic fixture's Lean model of `loans.md`: each operation returns the new state, or none for
a refused request; each clause of the prose has its theorems, and each theorem with hypotheses a
witness that they can hold. The ledger at the end names them; `lake env lean` on this file runs the
audit, which the complete fixture passes with no finding.
-/

namespace Loans
open SpecTools.Ledger

inductive Membership where
  | standard | premium
  deriving DecidableEq, Repr

def period : Membership → Nat
  | .standard => 14
  | .premium => 28

structure Loan where
  copy : Nat
  member : Nat
  due : Nat
  renewals : Nat
  deriving DecidableEq, Repr

structure State where
  loans : List Loan
  /-- Holds, as (copy, member). -/
  holds : List (Nat × Nat)
  fines : List (Nat × Nat)
  premium : List Nat

def State.fine (s : State) (m : Nat) : Nat := (s.fines.lookup m).getD 0
def State.membership (s : State) (m : Nat) : Membership := if m ∈ s.premium then .premium else .standard
def State.onLoan (s : State) (c : Nat) : Bool := s.loans.any (·.copy == c)
def State.count (s : State) (m : Nat) : Nat := (s.loans.filter (·.member == m)).length
def State.heldByOther (s : State) (c m : Nat) : Bool := s.holds.any fun h => h.1 == c && h.2 != m
def State.loanOf (s : State) (c : Nat) : Option Loan := s.loans.find? (·.copy == c)
def State.setFine (s : State) (m v : Nat) : State := { s with fines := (m, v) :: s.fines.filter (·.1 != m) }

def borrow (s : State) (m c today : Nat) : Option State :=
  if s.onLoan c || 5 ≤ s.count m || 10 ≤ s.fine m || s.heldByOther c m then none
  else some { s with
    loans := ⟨c, m, today + period (s.membership m), 0⟩ :: s.loans
    holds := s.holds.filter fun h => !(h.1 == c && h.2 == m) }

def renew (s : State) (m c today : Nat) : Option State :=
  match s.loanOf c with
  | none => none
  | some l =>
    if l.member != m || 2 ≤ l.renewals || s.heldByOther c m || l.due < today then none
    else some { s with loans := s.loans.map fun x =>
      if x.copy == c then { x with due := x.due + period (s.membership m), renewals := x.renewals + 1 }
      else x }

def giveBack (s : State) (c today : Nat) : State :=
  match s.loanOf c with
  | none => s
  | some l =>
    let s' := { s with loans := s.loans.filter (·.copy != c) }
    s'.setFine l.member (s.fine l.member + (today - l.due))

def placeHold (s : State) (m c : Nat) : Option State :=
  if !s.onLoan c || s.loans.any (fun l => l.copy == c && l.member == m) || s.holds.any (·.1 == c) then
    none
  else some { s with holds := (c, m) :: s.holds }

def pay (s : State) (m amount : Nat) : State := s.setFine m (s.fine m - amount)

/-- A request's effect: the new state, or the old one when it is refused. -/
def apply (s : State) (r : Option State) : State := r.getD s

/-! Borrowing -/

theorem borrow_free (s : State) (m c t : Nat) (free : s.onLoan c = false) (few : s.count m < 5)
    (clean : s.fine m < 10) (unheld : s.heldByOther c m = false) : (borrow s m c t).isSome := by
  have : ¬ 5 ≤ s.count m := by omega
  have : ¬ 10 ≤ s.fine m := by omega
  simp_all [borrow]

theorem borrow_on_loan (s : State) (m c t : Nat) (h : s.onLoan c = true) : borrow s m c t = none := by
  simp [borrow, h]

theorem borrow_at_limit (s : State) (m c t : Nat) (h : 5 ≤ s.count m) : borrow s m c t = none := by
  simp [borrow, h]

theorem borrow_count_le (s s' : State) (m c t : Nat) (h : borrow s m c t = some s') :
    s'.count m ≤ 5 := by
  unfold borrow at h
  split at h
  · cases h
  · rename_i hc
    cases h
    simp only [Bool.or_eq_true, not_or, State.count] at hc
    have hlt : ¬ 5 ≤ (s.loans.filter (·.member == m)).length := by
      have := hc.1.1.2
      intro h5
      exact this (decide_eq_true h5)
    simp only [State.count, List.filter_cons, beq_self_eq_true, ite_true, List.length_cons]
    omega

theorem borrow_owing (s : State) (m c t : Nat) (h : 10 ≤ s.fine m) : borrow s m c t = none := by
  simp [borrow, h]

theorem borrow_held (s : State) (m c t : Nat) (h : s.heldByOther c m = true) :
    borrow s m c t = none := by
  simp [borrow, h]

theorem borrow_ends_hold (s s' : State) (m c t : Nat) (h : borrow s m c t = some s') :
    (c, m) ∉ s'.holds := by
  unfold borrow at h
  split at h
  · cases h
  · cases h
    simp

theorem period_standard : period .standard = 14 := rfl
theorem period_premium : period .premium = 28 := rfl

theorem borrow_due (s s' : State) (m c t : Nat) (h : borrow s m c t = some s') :
    ∃ l ∈ s'.loans, l.copy = c ∧ l.member = m ∧ l.due = t + period (s.membership m) := by
  unfold borrow at h
  split at h
  · cases h
  · cases h
    exact ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩

/-! Renewing -/

theorem renew_limit (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : 2 ≤ l.renewals) : renew s m c t = none := by
  simp [renew, hl, h]

theorem renew_held (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : s.heldByOther c m = true) : renew s m c t = none := by
  simp [renew, hl, h]

theorem renew_moves_due (s s' : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : renew s m c t = some s') :
    ∃ x ∈ s'.loans, x.copy = c ∧ x.due = l.due + period (s.membership m) := by
  unfold renew at h
  rw [hl] at h
  simp only at h
  split at h
  · cases h
  · cases h
    have hmem : l ∈ s.loans := List.mem_of_find?_eq_some hl
    have hc : l.copy = c := by simpa using List.find?_some hl
    refine ⟨{ l with due := l.due + period (s.membership m), renewals := l.renewals + 1 },
      List.mem_map.mpr ⟨l, hmem, by simp [hc]⟩, hc, rfl⟩

theorem renew_late (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : l.due < t) : renew s m c t = none := by
  simp [renew, hl, h]

/-! Returning -/

theorem giveBack_ends (s : State) (c t : Nat) : (giveBack s c t).onLoan c = false := by
  unfold giveBack
  split
  · rename_i hn
    simp only [State.onLoan, List.any_eq_false, beq_iff_eq]
    intro l hl hc
    have := List.find?_eq_none.mp hn l hl
    simp_all [State.loanOf]
  · simp [State.setFine, State.onLoan]

theorem giveBack_fine (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l) :
    (giveBack s c t).fine l.member = s.fine l.member + (t - l.due) := by
  simp [giveBack, hl, State.setFine, State.fine]

theorem giveBack_on_time (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : t ≤ l.due) : (giveBack s c t).fine l.member = s.fine l.member := by
  rw [giveBack_fine s c t l hl]
  omega

theorem giveBack_not_on_loan (s : State) (c t : Nat) (h : s.loanOf c = none) : giveBack s c t = s := by
  simp [giveBack, h]

/-! Holds -/

theorem hold_on_loan (s : State) (m c : Nat) (lent : s.onLoan c = true)
    (notMine : s.loans.any (fun l => l.copy == c && l.member == m) = false)
    (none_ : s.holds.any (·.1 == c) = false) : (placeHold s m c).isSome := by
  simp [placeHold, lent, notMine, none_]

theorem hold_own (s : State) (m c : Nat) (h : s.loans.any (fun l => l.copy == c && l.member == m) = true) :
    placeHold s m c = none := by
  simp [placeHold, h]

theorem hold_one (s : State) (m c : Nat) (h : s.holds.any (·.1 == c) = true) : placeHold s m c = none := by
  simp [placeHold, h]

/-! Fines and refusals -/

theorem pay_reduces (s : State) (m a : Nat) : (pay s m a).fine m = s.fine m - a := by
  simp [pay, State.setFine, State.fine]

theorem refused_changes_nothing (s : State) : apply s none = s := rfl

/-! Witnesses: states meeting each theorem's hypotheses. -/

def empty : State := ⟨[], [], [], []⟩
def lent : State := ⟨[⟨7, 1, 14, 0⟩], [], [], []⟩
def heldLent : State := ⟨[⟨7, 1, 14, 2⟩], [(7, 2)], [(3, 12)], []⟩
def full : State := ⟨(List.range 5).map fun c => ⟨c, 1, 14, 0⟩, [], [], []⟩

theorem witness_free : empty.onLoan 7 = false ∧ empty.count 1 < 5 ∧ empty.fine 1 < 10 ∧
    empty.heldByOther 7 1 = false := by decide
theorem witness_lent : lent.onLoan 7 = true ∧ lent.loanOf 7 = some ⟨7, 1, 14, 0⟩ := by decide
theorem witness_full : 5 ≤ full.count 1 := by decide
theorem witness_owing : 10 ≤ heldLent.fine 3 := by decide
theorem witness_held : heldLent.heldByOther 7 1 = true ∧ heldLent.loanOf 7 = some ⟨7, 1, 14, 2⟩ ∧
    2 ≤ (⟨7, 1, 14, 2⟩ : Loan).renewals := by decide
theorem witness_borrowed : (borrow empty 1 7 0).isSome := by decide
theorem witness_renewed : (renew lent 1 7 3).isSome := by decide
theorem witness_late : lent.loanOf 7 = some ⟨7, 1, 14, 0⟩ ∧ (⟨7, 1, 14, 0⟩ : Loan).due < 20 := by decide
theorem witness_not_on_loan : empty.loanOf 7 = none := by decide
theorem witness_hold : lent.onLoan 7 = true ∧
    lent.loans.any (fun l => l.copy == 7 && l.member == 2) = false ∧
    lent.holds.any (·.1 == 7) = false := by decide
theorem witness_own : lent.loans.any (fun l => l.copy == 7 && l.member == 1) = true := by decide
theorem witness_one_hold : heldLent.holds.any (·.1 == 7) = true := by decide

def ledger : List Row := [
  { id := "borrow-free", clause := "A member may borrow a copy that is not on loan.",
    theorems := [``borrow_free], witnesses := [``witness_free] },
  { id := "never-two-borrowers", clause := "A copy on loan is never lent to a second member.",
    theorems := [``borrow_on_loan], witnesses := [``witness_lent] },
  { id := "five-copies", clause := "A member may have at most five copies on loan at once.",
    theorems := [``borrow_at_limit, ``borrow_count_le], witnesses := [``witness_full, ``witness_borrowed] },
  { id := "fines-block", clause := "A member who owes 10 or more in fines may not borrow.",
    theorems := [``borrow_owing], witnesses := [``witness_owing] },
  { id := "held-copy", clause := "A copy that another member holds may not be borrowed.",
    theorems := [``borrow_held], witnesses := [``witness_held] },
  { id := "hold-ends", clause := "When a member borrows a copy they hold, their hold on it ends.",
    theorems := [``borrow_ends_hold], witnesses := [``witness_borrowed] },
  { id := "period-standard", clause := "| standard | 14 days |", theorems := [``period_standard] },
  { id := "period-premium", clause := "| premium | 28 days |", theorems := [``period_premium] },
  { id := "due-date", clause := "A loan is due one loan period after the day it starts.",
    theorems := [``borrow_due], witnesses := [``witness_borrowed] },
  { id := "renew-limits", clause := "A loan may be renewed. It may be renewed at most twice, and \
      never while another member holds the copy.",
    theorems := [``renew_limit, ``renew_held], witnesses := [``witness_held, ``witness_renewed] },
  { id := "renew-moves-due", clause := "Renewing a loan moves its due date one loan period past the \
      old due date.", theorems := [``renew_moves_due], witnesses := [``witness_renewed, ``witness_lent] },
  { id := "renew-late", clause := "A loan cannot be renewed after its due date.",
    theorems := [``renew_late], witnesses := [``witness_late] },
  { id := "return-ends", clause := "Returning a copy ends its loan.", theorems := [``giveBack_ends] },
  { id := "late-fine", clause := "A copy returned after its due date adds a fine of 1 for each day late.",
    theorems := [``giveBack_fine], witnesses := [``witness_lent] },
  { id := "on-time", clause := "A copy returned on or before its due date adds no fine.",
    theorems := [``giveBack_on_time], witnesses := [``witness_lent] },
  { id := "return-unlent", clause := "Returning a copy that is not on loan changes nothing.",
    theorems := [``giveBack_not_on_loan], witnesses := [``witness_not_on_loan] },
  { id := "hold-lent", clause := "A member may hold a copy that is on loan to another member.",
    theorems := [``hold_on_loan], witnesses := [``witness_hold] },
  { id := "hold-own", clause := "A member may not hold a copy they have on loan.",
    theorems := [``hold_own], witnesses := [``witness_own] },
  { id := "one-hold", clause := "A copy has at most one hold.",
    theorems := [``hold_one], witnesses := [``witness_one_hold] },
  { id := "pay", clause := "Paying reduces a member's fines by the amount paid, and never below zero.",
    theorems := [``pay_reduces] },
  { id := "refusal", clause := "A request that is refused changes nothing.",
    theorems := [``refused_changes_nothing] }
]

end Loans

#eval SpecTools.Audit.run Loans.ledger `Loans
