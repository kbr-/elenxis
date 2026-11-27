-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Audit
import SpecTools.GapsRun
import SpecTools.Tests
import SpecTools.Replay

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
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

structure State where
  loans : List Loan
  /-- Holds, as (copy, member). -/
  holds : List (Nat × Nat)
  fines : List (Nat × Nat)
  premium : List Nat
  deriving DecidableEq, Lean.ToJson, Lean.FromJson

def State.fine (s : State) (m : Nat) : Nat := (s.fines.lookup m).getD 0
def State.membership (s : State) (m : Nat) : Membership := if m ∈ s.premium then .premium else .standard
def State.onLoan (s : State) (c : Nat) : Bool := s.loans.any (·.copy == c)
def State.count (s : State) (m : Nat) : Nat := (s.loans.filter (·.member == m)).length
def State.heldByOther (s : State) (c m : Nat) : Bool := s.holds.any fun h => h.1 == c && h.2 != m
def State.loanOf (s : State) (c : Nat) : Option Loan := s.loans.find? (·.copy == c)
def State.setFine (s : State) (m v : Nat) : State := { s with fines := (m, v) :: s.fines.filter (·.1 != m) }
/-- A member's loan limit: eight for a premium member who owes nothing, five otherwise. -/
def State.limit (s : State) (m : Nat) : Nat := if m ∈ s.premium ∧ s.fine m = 0 then 8 else 5
def State.overdue (s : State) (m today : Nat) : Bool := s.loans.any fun l => l.member == m && l.due < today
def State.holdCount (s : State) (m : Nat) : Nat := (s.holds.filter (·.2 == m)).length

def borrow (s : State) (m c today : Nat) : Option State :=
  if s.onLoan c || s.limit m ≤ s.count m || 10 ≤ s.fine m || s.heldByOther c m || s.overdue m today
  then none
  else some { s with
    loans := ⟨c, m, today + period (s.membership m), 0⟩ :: s.loans
    holds := s.holds.filter fun h => !(h.1 == c && h.2 == m) }

def renew (s : State) (m c today : Nat) : Option State :=
  match s.loanOf c with
  | none => none
  | some l =>
    if l.member != m || 2 ≤ l.renewals || s.heldByOther c m || l.due < today || 10 ≤ s.fine m then none
    else some { s with loans := s.loans.map fun x =>
      if x.copy == c then { x with due := x.due + period (s.membership m), renewals := x.renewals + 1 }
      else x }

def giveBack (s : State) (c today : Nat) : State :=
  match s.loanOf c with
  | none => s
  | some l =>
    let s' := { s with loans := s.loans.filter (·.copy != c) }
    s'.setFine l.member (s.fine l.member + min 30 (today - l.due))

def placeHold (s : State) (m c : Nat) : Option State :=
  if !s.onLoan c || s.loans.any (fun l => l.copy == c && l.member == m) || s.holds.any (·.1 == c)
    || 3 ≤ s.holdCount m || s.limit m ≤ s.count m + s.holdCount m then
    none
  else some { s with holds := (c, m) :: s.holds }

def pay (s : State) (m amount : Nat) : State := s.setFine m (s.fine m - amount)

/-! Borrowing -/

theorem borrow_free (s : State) (m c t : Nat) (free : s.onLoan c = false) (few : s.count m < s.limit m)
    (clean : s.fine m < 10) (unheld : s.heldByOther c m = false) (current : s.overdue m t = false) :
    (borrow s m c t).isSome := by
  have : ¬ s.limit m ≤ s.count m := by omega
  have : ¬ 10 ≤ s.fine m := by omega
  simp_all [borrow]

theorem borrow_on_loan (s : State) (m c t : Nat) (h : s.onLoan c = true) : borrow s m c t = none := by
  simp [borrow, h]

theorem borrow_at_limit (s : State) (m c t : Nat) (h : s.limit m ≤ s.count m) :
    borrow s m c t = none := by
  simp [borrow, h]

theorem limit_standard (s : State) (m : Nat) (h : m ∉ s.premium) : s.limit m = 5 := by
  simp [State.limit, h]

theorem limit_premium (s : State) (m : Nat) (h : m ∈ s.premium) (clean : s.fine m = 0) :
    s.limit m = 8 := by
  simp [State.limit, h, clean]

theorem limit_owing (s : State) (m : Nat) (h : 0 < s.fine m) : s.limit m = 5 := by
  have : s.fine m ≠ 0 := by omega
  simp [State.limit, this]

theorem borrow_count_le (s s' : State) (m c t : Nat) (h : borrow s m c t = some s') :
    s'.count m ≤ s.limit m := by
  unfold borrow at h
  split at h
  · cases h
  · rename_i hc
    cases h
    simp only [Bool.or_eq_true, not_or, State.count] at hc
    have hlt : ¬ s.limit m ≤ (s.loans.filter (·.member == m)).length := by
      have := hc.1.1.1.2
      intro h5
      exact this (decide_eq_true h5)
    simp only [State.count, List.filter_cons, beq_self_eq_true, ite_true, List.length_cons]
    omega

theorem borrow_overdue (s : State) (m c t : Nat) (h : s.overdue m t = true) :
    borrow s m c t = none := by
  simp [borrow, h]

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

theorem renew_allowed (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (mine : l.member = m) (few : l.renewals < 2) (unheld : s.heldByOther c m = false)
    (onTime : t ≤ l.due) (clean : s.fine m < 10) : (renew s m c t).isSome := by
  have h1 : ¬ 2 ≤ l.renewals := by omega
  have h2 : ¬ l.due < t := by omega
  have h3 : ¬ 10 ≤ s.fine m := by omega
  simp [renew, hl, mine, h1, h2, h3, unheld]

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

theorem renew_not_borrower (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : l.member ≠ m) : renew s m c t = none := by
  simp [renew, hl, h]

theorem renew_owing (s : State) (m c t : Nat) (h : 10 ≤ s.fine m) : renew s m c t = none := by
  unfold renew
  split
  · rfl
  · simp [h]

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
    (giveBack s c t).fine l.member = s.fine l.member + min 30 (t - l.due) := by
  simp [giveBack, hl, State.setFine, State.fine]

theorem giveBack_fine_le (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l) :
    (giveBack s c t).fine l.member ≤ s.fine l.member + 30 := by
  rw [giveBack_fine s c t l hl]
  omega

theorem giveBack_on_time (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
    (h : t ≤ l.due) : (giveBack s c t).fine l.member = s.fine l.member := by
  rw [giveBack_fine s c t l hl]
  omega

theorem giveBack_not_on_loan (s : State) (c t : Nat) (h : s.loanOf c = none) : giveBack s c t = s := by
  simp [giveBack, h]

/-! Holds -/

theorem hold_on_loan (s : State) (m c : Nat) (lent : s.onLoan c = true)
    (notMine : s.loans.any (fun l => l.copy == c && l.member == m) = false)
    (none_ : s.holds.any (·.1 == c) = false) (few : s.holdCount m < 3)
    (room : s.count m + s.holdCount m < s.limit m) : (placeHold s m c).isSome := by
  have : ¬ 3 ≤ s.holdCount m := by omega
  have : ¬ s.limit m ≤ s.count m + s.holdCount m := by omega
  simp [placeHold, lent, notMine, none_, *]

theorem hold_three (s : State) (m c : Nat) (h : 3 ≤ s.holdCount m) : placeHold s m c = none := by
  simp [placeHold, h]

theorem hold_at_limit (s : State) (m c : Nat) (h : s.limit m ≤ s.count m + s.holdCount m) :
    placeHold s m c = none := by
  simp [placeHold, h]

theorem hold_not_lent (s : State) (m c : Nat) (h : s.onLoan c = false) : placeHold s m c = none := by
  simp [placeHold, h]

theorem hold_own (s : State) (m c : Nat) (h : s.loans.any (fun l => l.copy == c && l.member == m) = true) :
    placeHold s m c = none := by
  simp [placeHold, h]

theorem hold_one (s : State) (m c : Nat) (h : s.holds.any (·.1 == c) = true) : placeHold s m c = none := by
  simp [placeHold, h]

/-! Fines -/

theorem pay_reduces (s : State) (m a : Nat) : (pay s m a).fine m = s.fine m - a := by
  simp [pay, State.setFine, State.fine]

/-! Witnesses: states meeting each theorem's hypotheses. -/

def empty : State := ⟨[], [], [], []⟩
def lent : State := ⟨[⟨7, 1, 14, 0⟩], [], [], []⟩
def heldLent : State := ⟨[⟨7, 1, 14, 2⟩], [(7, 2)], [(3, 12)], []⟩
def full : State := ⟨(List.range 5).map fun c => ⟨c, 1, 14, 0⟩, [], [], []⟩

def premiumFull : State := ⟨(List.range 5).map fun c => ⟨c, 1, 14, 0⟩, [], [], [1]⟩
def premiumOwing : State := ⟨[], [], [(1, 3)], [1]⟩
def owingLent : State := ⟨[⟨7, 1, 14, 0⟩], [], [(1, 12)], []⟩
def threeHolds : State := ⟨[⟨7, 1, 14, 0⟩, ⟨8, 1, 14, 0⟩, ⟨9, 1, 14, 0⟩], [(7, 2), (8, 2), (9, 2)], [], []⟩
def busy : State :=
  ⟨[⟨1, 2, 14, 0⟩, ⟨2, 2, 14, 0⟩, ⟨3, 2, 14, 0⟩, ⟨7, 1, 14, 0⟩, ⟨8, 1, 14, 0⟩], [(7, 2), (8, 2)], [], []⟩

theorem witness_borrow_free :
    ∃ (s : State) (m c t : Nat) (free : s.onLoan c = false)
      (few : s.count m < s.limit m) (clean : s.fine m < 10)
      (unheld : s.heldByOther c m = false) (current : s.overdue m t = false), True :=
  ⟨empty, 1, 7, 0, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem witness_borrow_on_loan :
    ∃ (s : State) (m c t : Nat) (h : s.onLoan c = true), True :=
  ⟨lent, 2, 7, 0, by decide, trivial⟩

theorem witness_borrow_at_limit :
    ∃ (s : State) (m c t : Nat) (h : s.limit m ≤ s.count m), True :=
  ⟨full, 1, 7, 0, by decide, trivial⟩

theorem witness_limit_standard :
    ∃ (s : State) (m : Nat) (h : m ∉ s.premium), True :=
  ⟨full, 1, by decide, trivial⟩

theorem witness_limit_premium :
    ∃ (s : State) (m : Nat) (h : m ∈ s.premium) (clean : s.fine m = 0), True :=
  ⟨premiumFull, 1, by decide, by decide, trivial⟩

theorem witness_limit_owing :
    ∃ (s : State) (m : Nat) (h : 0 < s.fine m), True :=
  ⟨premiumOwing, 1, by decide, trivial⟩

theorem witness_borrow_count_le :
    ∃ (s s' : State) (m c t : Nat) (h : borrow s m c t = some s'), True :=
  ⟨empty, ⟨[⟨7, 1, 14, 0⟩], [], [], []⟩, 1, 7, 0, by decide, trivial⟩

theorem witness_borrow_overdue :
    ∃ (s : State) (m c t : Nat) (h : s.overdue m t = true), True :=
  ⟨lent, 1, 8, 20, by decide, trivial⟩

theorem witness_borrow_owing :
    ∃ (s : State) (m c t : Nat) (h : 10 ≤ s.fine m), True :=
  ⟨owingLent, 1, 7, 0, by decide, trivial⟩

theorem witness_borrow_held :
    ∃ (s : State) (m c t : Nat) (h : s.heldByOther c m = true), True :=
  ⟨heldLent, 1, 7, 0, by decide, trivial⟩

theorem witness_renew_allowed :
    ∃ (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
      (mine : l.member = m) (few : l.renewals < 2)
      (unheld : s.heldByOther c m = false) (onTime : t ≤ l.due)
      (clean : s.fine m < 10), True :=
  ⟨lent, 1, 7, 3, ⟨7, 1, 14, 0⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, trivial⟩

theorem witness_renew_limit :
    ∃ (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
      (h : 2 ≤ l.renewals), True :=
  ⟨heldLent, 1, 7, 3, ⟨7, 1, 14, 2⟩, by decide, by decide, trivial⟩

theorem witness_renew_held :
    ∃ (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
      (h : s.heldByOther c m = true), True :=
  ⟨heldLent, 1, 7, 3, ⟨7, 1, 14, 2⟩, by decide, by decide, trivial⟩

theorem witness_renew_moves_due :
    ∃ (s s' : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
      (h : renew s m c t = some s'), True :=
  ⟨lent, ⟨[⟨7, 1, 28, 1⟩], [], [], []⟩, 1, 7, 3, ⟨7, 1, 14, 0⟩, by decide, by decide, trivial⟩

theorem witness_renew_late :
    ∃ (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l) (h : l.due < t), True :=
  ⟨lent, 1, 7, 20, ⟨7, 1, 14, 0⟩, by decide, by decide, trivial⟩

theorem witness_renew_not_borrower :
    ∃ (s : State) (m c t : Nat) (l : Loan) (hl : s.loanOf c = some l)
      (h : l.member ≠ m), True :=
  ⟨lent, 2, 7, 3, ⟨7, 1, 14, 0⟩, by decide, by decide, trivial⟩

theorem witness_giveBack_fine :
    ∃ (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l), True :=
  ⟨lent, 7, 20, ⟨7, 1, 14, 0⟩, by decide, trivial⟩

theorem witness_giveBack_on_time :
    ∃ (s : State) (c t : Nat) (l : Loan) (hl : s.loanOf c = some l) (h : t ≤ l.due), True :=
  ⟨lent, 7, 14, ⟨7, 1, 14, 0⟩, by decide, by decide, trivial⟩

theorem witness_giveBack_not_on_loan :
    ∃ (s : State) (c t : Nat) (h : s.loanOf c = none), True :=
  ⟨empty, 7, 0, by decide, trivial⟩

theorem witness_hold_on_loan :
    ∃ (s : State) (m c : Nat) (lent : s.onLoan c = true)
      (notMine : s.loans.any (fun l => l.copy == c && l.member == m) = false)
      (none_ : s.holds.any (·.1 == c) = false) (few : s.holdCount m < 3)
      (room : s.count m + s.holdCount m < s.limit m), True :=
  ⟨lent, 2, 7, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem witness_hold_not_lent :
    ∃ (s : State) (m c : Nat) (h : s.onLoan c = false), True :=
  ⟨empty, 2, 7, by decide, trivial⟩

theorem witness_hold_own :
    ∃ (s : State) (m c : Nat)
      (h : s.loans.any (fun l => l.copy == c && l.member == m) = true), True :=
  ⟨lent, 1, 7, by decide, trivial⟩

theorem witness_hold_one :
    ∃ (s : State) (m c : Nat) (h : s.holds.any (·.1 == c) = true), True :=
  ⟨heldLent, 3, 7, by decide, trivial⟩

theorem witness_hold_three :
    ∃ (s : State) (m c : Nat) (h : 3 ≤ s.holdCount m), True :=
  ⟨threeHolds, 2, 10, by decide, trivial⟩

theorem witness_hold_at_limit :
    ∃ (s : State) (m c : Nat) (h : s.limit m ≤ s.count m + s.holdCount m), True :=
  ⟨busy, 2, 7, by decide, trivial⟩

/-- The Python property test covering each row, in `test_loans.py`. -/
def pythonTest : String → List String
  | "period-standard" | "period-premium" => ["test_periods"]
  | id => ["test_" ++ id.replace "-" "_"]

def rows : List Row := [
  { id := "borrow-free", clause := "A member may borrow a copy that is not on loan.",
    theorems := [``borrow_free],
    evidence := [⟨``borrow_free, ``witness_borrow_free, .inhabited⟩] },
  { id := "never-two-borrowers", clause := "A copy on loan is never lent to a second member.",
    theorems := [``borrow_on_loan],
    evidence := [⟨``borrow_on_loan, ``witness_borrow_on_loan, .inhabited⟩] },
  { id := "five-copies", clause := "A standard member may have at most five copies on loan at once.",
    theorems := [``borrow_at_limit, ``limit_standard, ``borrow_count_le],
    evidence := [⟨``borrow_at_limit, ``witness_borrow_at_limit, .inhabited⟩,
      ⟨``limit_standard, ``witness_limit_standard, .inhabited⟩,
      ⟨``borrow_count_le, ``witness_borrow_count_le, .inhabited⟩] },
  { id := "premium-eight", clause := "A premium member may have at most eight copies on loan at once.",
    theorems := [``borrow_at_limit, ``limit_premium, ``borrow_count_le],
    evidence := [⟨``borrow_at_limit, ``witness_borrow_at_limit, .inhabited⟩,
      ⟨``limit_premium, ``witness_limit_premium, .inhabited⟩,
      ⟨``borrow_count_le, ``witness_borrow_count_le, .inhabited⟩] },
  { id := "premium-owing", clause := "A premium member who owes any fine may have no more copies on \
      loan than a standard member.",
    theorems := [``borrow_at_limit, ``limit_owing],
    evidence := [⟨``borrow_at_limit, ``witness_borrow_at_limit, .inhabited⟩,
      ⟨``limit_owing, ``witness_limit_owing, .inhabited⟩] },
  { id := "fines-block", clause := "A member who owes 10 or more in fines may not borrow.",
    theorems := [``borrow_owing],
    evidence := [⟨``borrow_owing, ``witness_borrow_owing, .inhabited⟩] },
  { id := "overdue-blocks", clause := "A member with a loan past its due date may not borrow.",
    theorems := [``borrow_overdue],
    evidence := [⟨``borrow_overdue, ``witness_borrow_overdue, .inhabited⟩] },
  { id := "held-copy", clause := "A copy that another member holds may not be borrowed.",
    theorems := [``borrow_held],
    evidence := [⟨``borrow_held, ``witness_borrow_held, .inhabited⟩] },
  { id := "hold-ends", clause := "When a member borrows a copy they hold, their hold on it ends.",
    theorems := [``borrow_ends_hold],
    evidence := [⟨``borrow_ends_hold, ``witness_borrow_count_le, .inhabited⟩] },
  { id := "period-standard", clause := "| standard | 14 days |", theorems := [``period_standard] },
  { id := "period-premium", clause := "| premium | 28 days |", theorems := [``period_premium] },
  { id := "due-date", clause := "A loan is due one loan period after the day it starts.",
    theorems := [``borrow_due],
    evidence := [⟨``borrow_due, ``witness_borrow_count_le, .inhabited⟩] },
  { id := "renew-limits", clause := "A loan may be renewed. It may be renewed at most twice, and \
      never while another member holds the copy.",
    theorems := [``renew_allowed, ``renew_limit, ``renew_held],
    evidence := [⟨``renew_allowed, ``witness_renew_allowed, .inhabited⟩,
      ⟨``renew_limit, ``witness_renew_limit, .inhabited⟩,
      ⟨``renew_held, ``witness_renew_held, .inhabited⟩] },
  { id := "renew-moves-due", clause := "Renewing a loan moves its due date one loan period past the \
      old due date.", theorems := [``renew_moves_due],
    evidence := [⟨``renew_moves_due, ``witness_renew_moves_due, .inhabited⟩] },
  { id := "renew-late", clause := "A loan cannot be renewed after its due date.",
    theorems := [``renew_late],
    evidence := [⟨``renew_late, ``witness_renew_late, .inhabited⟩] },
  { id := "renew-borrower", clause := "Only the member who has a loan may renew it.",
    theorems := [``renew_not_borrower],
    evidence := [⟨``renew_not_borrower, ``witness_renew_not_borrower, .inhabited⟩] },
  { id := "renew-owing", clause := "A member who owes 10 or more in fines may not renew.",
    theorems := [``renew_owing],
    evidence := [⟨``renew_owing, ``witness_borrow_owing, .inhabited⟩] },
  { id := "return-ends", clause := "Returning a copy ends its loan.", theorems := [``giveBack_ends] },
  { id := "late-fine", clause := "A copy returned after its due date adds a fine of 1 for each day late.",
    theorems := [``giveBack_fine],
    evidence := [⟨``giveBack_fine, ``witness_giveBack_fine, .inhabited⟩] },
  { id := "fine-cap", clause := "The fine for one late return is at most 30.",
    theorems := [``giveBack_fine_le, ``giveBack_fine],
    evidence := [⟨``giveBack_fine_le, ``witness_giveBack_fine, .inhabited⟩,
      ⟨``giveBack_fine, ``witness_giveBack_fine, .inhabited⟩] },
  { id := "on-time", clause := "A copy returned on or before its due date adds no fine.",
    theorems := [``giveBack_on_time],
    evidence := [⟨``giveBack_on_time, ``witness_giveBack_on_time, .inhabited⟩] },
  { id := "return-unlent", clause := "Returning a copy that is not on loan changes nothing.",
    theorems := [``giveBack_not_on_loan],
    evidence := [⟨``giveBack_not_on_loan, ``witness_giveBack_not_on_loan, .inhabited⟩] },
  { id := "hold-lent", clause := "A member may hold a copy that is on loan to another member.",
    theorems := [``hold_on_loan],
    evidence := [⟨``hold_on_loan, ``witness_hold_on_loan, .inhabited⟩] },
  { id := "hold-unlent", clause := "A copy that is not on loan can't be held.",
    theorems := [``hold_not_lent],
    evidence := [⟨``hold_not_lent, ``witness_hold_not_lent, .inhabited⟩] },
  { id := "hold-own", clause := "A member may not hold a copy they have on loan.",
    theorems := [``hold_own],
    evidence := [⟨``hold_own, ``witness_hold_own, .inhabited⟩] },
  { id := "one-hold", clause := "A copy has at most one hold.",
    theorems := [``hold_one],
    evidence := [⟨``hold_one, ``witness_hold_one, .inhabited⟩] },
  { id := "three-holds", clause := "A member may hold at most three copies.",
    theorems := [``hold_three],
    evidence := [⟨``hold_three, ``witness_hold_three, .inhabited⟩] },
  { id := "hold-limit", clause := "A member may not place a hold while their loans and holds together \
      reach their loan limit.",
    theorems := [``hold_at_limit],
    evidence := [⟨``hold_at_limit, ``witness_hold_at_limit, .inhabited⟩] },
  { id := "pay", clause := "Paying reduces a member's fines by the amount paid, and never below zero.",
    theorems := [``pay_reduces] }
]

def ledger : List Row := rows.map fun r => { r with tests := pythonTest r.id }

inductive Operation where
  | borrow (member copy today : Nat)
  | renew (member copy today : Nat)
  | giveBack (copy today : Nat)
  | hold (member copy : Nat)
  | pay (member amount : Nat)

def operationJson (name : String) (fields : List (String × Nat)) : Lean.Json :=
  Lean.Json.mkObj (("kind", Lean.toJson name) ::
    fields.map fun (key, value) => (key, Lean.toJson value))

instance : Lean.ToJson Operation where
  toJson
    | .borrow m c t => operationJson "borrow" [("member", m), ("copy", c), ("today", t)]
    | .renew m c t => operationJson "renew" [("member", m), ("copy", c), ("today", t)]
    | .giveBack c t => operationJson "return" [("copy", c), ("today", t)]
    | .hold m c => operationJson "hold" [("member", m), ("copy", c)]
    | .pay m a => operationJson "pay" [("member", m), ("amount", a)]

def replayStep (s : State) : Operation → Option State
  | .borrow m c t => borrow s m c t
  | .renew m c t => renew s m c t
  | .giveBack c t => some (giveBack s c t)
  | .hold m c => placeHold s m c
  | .pay m a => some (pay s m a)

/-- Fines are keyed by member and premium status is membership in a set. -/
def replaySnapshot (s : State) : State :=
  { s with fines := s.fines.mergeSort (fun l r => l.1 < r.1 || (l.1 == r.1 && l.2 ≤ r.2))
           premium := s.premium.eraseDups.mergeSort }

def replayTrace : SpecTools.Replay.Trace State Operation :=
  ⟨empty, .borrow 1 7 0,
    [.borrow 2 7 1, .renew 1 7 11, .hold 2 7, .giveBack 7 35, .pay 1 4, .borrow 2 7 36]⟩

end Loans

#eval SpecTools.Audit.run Loans.ledger `Loans

-- The fixture's directory (`SPEC_TOOLS_DIR`, for a copy) and the adapter (`SPEC_TOOLS_ADAPTER`).
def fixtureDir : IO String := return (← IO.getEnv "SPEC_TOOLS_DIR").getD "fixtures/loans"
def adapterPath : IO String :=
  return (← IO.getEnv "SPEC_TOOLS_ADAPTER").getD "../../adapters/python_guards.py"

def replayAdapterPath : IO String :=
  return (← IO.getEnv "SPEC_TOOLS_REPLAY_ADAPTER").getD "../../adapters/loans_replay.py"

-- With `SPEC_TOOLS_TESTS` set, the Python tests against the guards of `loans.py`.
#eval show IO Unit from do
  if (← IO.getEnv "SPEC_TOOLS_TESTS").isSome then
    let dir ← fixtureDir
    SpecTools.Tests.run Loans.ledger (← adapterPath) "loans.py" "test_loans.py" (cwd := some dir)
      (replay := SpecTools.Replay.run Loans.replayTrace Loans.replayStep Loans.replaySnapshot
        (← replayAdapterPath) dir)

-- With `SPEC_TOOLS_GAPS` set to a model, the gaps against `loans.md` too (a live call), on the
-- backend `SPEC_TOOLS_BACKEND` configures, with that model.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  if let some model ← IO.getEnv "SPEC_TOOLS_GAPS" then
    SpecTools.Gaps.run Loans.ledger (← IO.FS.readFile (System.FilePath.mk (← fixtureDir) / "loans.md"))
      (← SpecTools.Model.selectedBackend "configured" model)
