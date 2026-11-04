"""The synthetic fixture's Python implementation of loans.md, the same operations as Loans.lean.

Each operation returns the new state, or None for a refused request; states are immutable.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace

PERIOD = {"standard": 14, "premium": 28}
MAX_LOANS = 5
FINE_LIMIT = 10
MAX_RENEWALS = 2


@dataclass(frozen=True)
class Loan:
    copy: int
    member: int
    due: int
    renewals: int = 0


@dataclass(frozen=True)
class State:
    loans: tuple[Loan, ...] = ()
    holds: tuple[tuple[int, int], ...] = ()  # (copy, member)
    fines: tuple[tuple[int, int], ...] = ()  # (member, amount)
    premium: frozenset[int] = field(default_factory=frozenset)

    def fine(self, member: int) -> int:
        return next((amount for m, amount in self.fines if m == member), 0)

    def membership(self, member: int) -> str:
        return "premium" if member in self.premium else "standard"

    def on_loan(self, copy: int) -> bool:
        return any(loan.copy == copy for loan in self.loans)

    def count(self, member: int) -> int:
        return sum(1 for loan in self.loans if loan.member == member)

    def held_by_other(self, copy: int, member: int) -> bool:
        return any(c == copy and m != member for c, m in self.holds)

    def loan_of(self, copy: int) -> Loan | None:
        return next((loan for loan in self.loans if loan.copy == copy), None)

    def with_fine(self, member: int, amount: int) -> State:
        return replace(self, fines=((member, amount),) + tuple(f for f in self.fines if f[0] != member))


def borrow(state: State, member: int, copy: int, today: int) -> State | None:
    if (state.on_loan(copy) or state.count(member) >= MAX_LOANS or state.fine(member) >= FINE_LIMIT
            or state.held_by_other(copy, member)):
        return None
    loan = Loan(copy, member, today + PERIOD[state.membership(member)])
    return replace(state, loans=(loan,) + state.loans,
                   holds=tuple(h for h in state.holds if h != (copy, member)))


def renew(state: State, member: int, copy: int, today: int) -> State | None:
    loan = state.loan_of(copy)
    if (loan is None or loan.member != member or loan.renewals >= MAX_RENEWALS
            or state.held_by_other(copy, member) or loan.due < today):
        return None
    period = PERIOD[state.membership(member)]
    return replace(state, loans=tuple(
        replace(x, due=x.due + period, renewals=x.renewals + 1) if x.copy == copy else x
        for x in state.loans))


def give_back(state: State, copy: int, today: int) -> State:
    loan = state.loan_of(copy)
    if loan is None:
        return state
    rest = replace(state, loans=tuple(x for x in state.loans if x.copy != copy))
    return rest.with_fine(loan.member, state.fine(loan.member) + max(0, today - loan.due))


def place_hold(state: State, member: int, copy: int) -> State | None:
    if (not state.on_loan(copy) or any(x.copy == copy and x.member == member for x in state.loans)
            or any(c == copy for c, _ in state.holds)):
        return None
    return replace(state, holds=((copy, member),) + state.holds)


def pay(state: State, member: int, amount: int) -> State:
    return state.with_fine(member, max(0, state.fine(member) - amount))
