"""Property tests of loans.py, one or more per clause of loans.md, named by the ledger row they cover.

The domain: states built by applying random requests to an empty library of copies 0 to 9 and
members 0 to 4 (member 4 premium), so every state is one the library can reach. A property about a
case random requests rarely reach (a member at the limit, a fine, another member's hold) builds that
case onto the state, so every example meets the property's condition.
"""

from __future__ import annotations

from dataclasses import replace

from hypothesis import given, settings, strategies as st

from loans import (FINE_LIMIT, MAX_LOANS, MAX_RENEWALS, PERIOD, Loan, State, borrow, give_back,
                   pay, place_hold, renew)

settings.register_profile("fixture", database=None)
settings.load_profile("fixture")

COPIES = st.integers(0, 9)
MEMBERS = st.integers(0, 4)
DAYS = st.integers(0, 120)
# Borrowing weighted, and member 0 favoured, so states hold loans of several members.
REQUEST = st.tuples(st.sampled_from(["borrow"] * 4 + ["renew", "return", "hold", "pay"]),
                    st.one_of(st.just(0), MEMBERS), COPIES, st.integers(0, 20))
SPARE = 100  # copies from here on are never in a generated state


def run(requests: list[tuple[str, int, int, int]]) -> State:
    state, today = State(premium=frozenset({4})), 0
    for kind, member, copy, n in requests:
        today += n % 4
        result = {"borrow": lambda: borrow(state, member, copy, today),
                  "renew": lambda: renew(state, member, copy, today),
                  "return": lambda: give_back(state, copy, today + n),
                  "hold": lambda: place_hold(state, member, copy),
                  "pay": lambda: pay(state, member, n)}[kind]()
        state = result if result is not None else state
    return state


STATES = st.lists(REQUEST, max_size=60).map(run)


def with_loan(s: State, loan: Loan) -> State:
    return replace(s, loans=(loan,) + s.loans)


def at_limit(s: State, m: int) -> State:
    for i in range(MAX_LOANS - s.count(m)):
        s = with_loan(s, Loan(SPARE + i, m, 14))
    return s


def other(m: int) -> int:
    return (m + 1) % 5


@given(STATES, MEMBERS, COPIES, DAYS)
def test_borrow_free(s, m, c, t):  # borrow-free
    if not s.on_loan(c) and s.count(m) < MAX_LOANS and s.fine(m) < FINE_LIMIT and not s.held_by_other(c, m):
        assert borrow(s, m, c, t) is not None
    fresh = State()
    assert borrow(fresh, m, c, t) is not None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_never_two_borrowers(s, m, c, t):  # never-two-borrowers
    if s.on_loan(c):
        assert borrow(s, m, c, t) is None
    assert borrow(with_loan(s, Loan(SPARE, other(m), 14)), m, SPARE, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_five_copies(s, m, c, t):  # five-copies
    assert borrow(at_limit(s, m), m, c, t) is None
    after = borrow(s, m, c, t)
    if after is not None:
        assert after.count(m) <= MAX_LOANS


@given(STATES, MEMBERS, COPIES, DAYS, st.integers(FINE_LIMIT, 50))
def test_fines_block(s, m, c, t, f):  # fines-block
    assert borrow(s.with_fine(m, f), m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_held_copy(s, m, c, t):  # held-copy
    held = replace(s, holds=((c, other(m)),) + s.holds)
    assert borrow(held, m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_hold_ends(s, m, c, t):  # hold-ends
    after = borrow(replace(s, holds=((c, m),) + s.holds), m, c, t)
    if after is not None:
        assert (c, m) not in after.holds


def test_periods():  # period-standard, period-premium
    assert PERIOD == {"standard": 14, "premium": 28}


@given(STATES, MEMBERS, COPIES, DAYS)
def test_due_date(s, m, c, t):  # due-date
    after = borrow(s, m, c, t)
    if after is not None:
        assert after.loan_of(c).due == t + PERIOD[s.membership(m)]


@given(STATES, MEMBERS, DAYS, st.integers(0, MAX_RENEWALS - 1))
def test_renew_limits(s, m, d, r):  # renew-limits
    mine = with_loan(s, Loan(SPARE, m, d, r))
    assert renew(mine, m, SPARE, d) is not None
    assert renew(with_loan(s, Loan(SPARE, m, d, MAX_RENEWALS)), m, SPARE, d) is None
    assert renew(replace(mine, holds=((SPARE, other(m)),) + mine.holds), m, SPARE, d) is None


@given(STATES, MEMBERS, DAYS)
def test_renew_moves_due(s, m, d):  # renew-moves-due
    mine = with_loan(s, Loan(SPARE, m, d))
    assert renew(mine, m, SPARE, d).loan_of(SPARE).due == d + PERIOD[s.membership(m)]


@given(STATES, MEMBERS, DAYS, st.integers(1, 30))
def test_renew_late(s, m, d, late):  # renew-late
    assert renew(with_loan(s, Loan(SPARE, m, d)), m, SPARE, d + late) is None


@given(STATES, MEMBERS, DAYS)
def test_renew_borrower(s, m, d):  # renew-borrower
    assert renew(with_loan(s, Loan(SPARE, other(m), d)), m, SPARE, d) is None


@given(STATES, COPIES, DAYS)
def test_return_ends(s, c, t):  # return-ends
    assert not give_back(s, c, t).on_loan(c)


@given(STATES, MEMBERS, DAYS, st.integers(0, 30))
def test_late_fine(s, m, d, late):  # late-fine
    lent = with_loan(s, Loan(SPARE, m, d))
    assert give_back(lent, SPARE, d + late).fine(m) == s.fine(m) + late


@given(STATES, MEMBERS, DAYS, st.integers(0, 30))
def test_on_time(s, m, d, early):  # on-time
    lent = with_loan(s, Loan(SPARE, m, d + early))
    assert give_back(lent, SPARE, d).fine(m) == s.fine(m)


@given(STATES, DAYS)
def test_return_unlent(s, t):  # return-unlent
    assert give_back(s, SPARE, t) == s


@given(STATES, MEMBERS)
def test_hold_lent(s, m):  # hold-lent
    assert place_hold(with_loan(s, Loan(SPARE, other(m), 14)), m, SPARE) is not None


@given(STATES, MEMBERS)
def test_hold_unlent(s, m):  # hold-unlent
    assert place_hold(s, m, SPARE) is None


@given(STATES, MEMBERS)
def test_hold_own(s, m):  # hold-own
    assert place_hold(with_loan(s, Loan(SPARE, m, 14)), m, SPARE) is None


@given(STATES, MEMBERS)
def test_one_hold(s, m):  # one-hold
    lent = with_loan(s, Loan(SPARE, other(m), 14))
    held = replace(lent, holds=((SPARE, other(other(m))),) + lent.holds)
    assert place_hold(held, m, SPARE) is None
    after = place_hold(lent, m, SPARE)
    assert after is not None and sum(1 for h in after.holds if h[0] == SPARE) == 1


@given(STATES, MEMBERS, st.integers(0, 50))
def test_pay(s, m, a):  # pay
    assert pay(s, m, a).fine(m) == max(0, s.fine(m) - a)


@settings(max_examples=50)
@given(STATES, MEMBERS, COPIES, DAYS)
def test_refusal(s, m, c, t):  # refusal
    for result in (borrow(s, m, c, t), renew(s, m, c, t), place_hold(s, m, c)):
        assert result is None or isinstance(result, State)
