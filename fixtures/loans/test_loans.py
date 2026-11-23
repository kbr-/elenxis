# CONFESSION: the fixture's implementation is Python, so its property tests run under pytest and Hypothesis.
"""Property tests of loans.py, one or more per clause of loans.md, named by the ledger row they cover.

The domain: states built by applying random requests to an empty library of copies 0 to 9 and
members 0 to 4 (member 4 premium), so every state is one the library can reach. A property about a
case random requests rarely reach (a member at the limit, a fine, another member's hold) builds that
case onto the state, and a property about one guard first clears the member's loans, holds and
fines (`clean`), so no other guard refuses the request in its place.
"""

from __future__ import annotations

from dataclasses import replace

from hypothesis import given, settings, strategies as st

from loans import (FINE_CAP, FINE_LIMIT, MAX_HOLDS, MAX_LOANS, MAX_RENEWALS, PERIOD, PREMIUM_LOANS,
                   Loan, State, borrow, give_back, pay, place_hold, renew)

settings.register_profile("fixture", database=None)
settings.load_profile("fixture")

COPIES = st.integers(0, 9)
MEMBERS = st.integers(0, 4)
DAYS = st.integers(0, 120)
# Borrowing weighted, and member 0 favoured, so states hold loans of several members.
REQUEST = st.tuples(st.sampled_from(["borrow"] * 4 + ["renew", "return", "hold", "pay"]),
                    st.one_of(st.just(0), MEMBERS), COPIES, st.integers(0, 20))
SPARE = 100  # copies from here on are never in a generated state
FAR = 1000  # a due date no generated day reaches


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


def clean(s: State, m: int) -> State:
    """The state with member m's loans, holds and fines removed."""
    return replace(s, loans=tuple(x for x in s.loans if x.member != m),
                   holds=tuple(h for h in s.holds if h[1] != m),
                   fines=tuple(f for f in s.fines if f[0] != m))


def loans_of(s: State, m: int, n: int) -> State:
    for i in range(n):
        s = with_loan(s, Loan(SPARE + 10 + i, m, FAR))
    return s


def at_limit(s: State, m: int) -> State:
    return loans_of(s, m, s.limit(m) - s.count(m))


def other(m: int) -> int:
    return (m + 1) % 5


def standard(s: State, m: int) -> State:
    return replace(s, premium=s.premium - {m})


def premium(s: State, m: int) -> State:
    return replace(s, premium=s.premium | {m})


@given(STATES, MEMBERS, COPIES, DAYS)
def test_borrow_free(s, m, c, t):  # borrow-free
    if (not s.on_loan(c) and s.count(m) < s.limit(m) and s.fine(m) < FINE_LIMIT
            and not s.held_by_other(c, m) and not s.overdue(m, t)):
        assert borrow(s, m, c, t) is not None
    assert borrow(clean(s, m), m, SPARE, t) is not None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_never_two_borrowers(s, m, c, t):  # never-two-borrowers
    if s.on_loan(c):
        assert borrow(s, m, c, t) is None
    assert borrow(with_loan(clean(s, m), Loan(SPARE, other(m), FAR)), m, SPARE, t) is None


@given(STATES, MEMBERS, DAYS)
def test_five_copies(s, m, t):  # five-copies
    base = standard(clean(s, m), m)
    assert borrow(loans_of(base, m, MAX_LOANS - 1), m, SPARE, t) is not None
    assert borrow(loans_of(base, m, MAX_LOANS), m, SPARE, t) is None
    after = borrow(s, m, SPARE, t)
    if after is not None:
        assert after.count(m) <= after.limit(m)


@given(STATES, MEMBERS, DAYS)
def test_premium_eight(s, m, t):  # premium-eight
    base = premium(clean(s, m), m)
    assert borrow(loans_of(base, m, PREMIUM_LOANS - 1), m, SPARE, t) is not None
    assert borrow(loans_of(base, m, PREMIUM_LOANS), m, SPARE, t) is None


@given(STATES, MEMBERS, DAYS, st.integers(1, FINE_LIMIT - 1))
def test_premium_owing(s, m, t, f):  # premium-owing
    base = premium(clean(s, m), m).with_fine(m, f)
    assert borrow(loans_of(base, m, MAX_LOANS - 1), m, SPARE, t) is not None
    assert borrow(loans_of(base, m, MAX_LOANS), m, SPARE, t) is None


@given(STATES, MEMBERS, DAYS, st.integers(FINE_LIMIT, 50))
def test_fines_block(s, m, t, f):  # fines-block
    assert borrow(clean(s, m).with_fine(m, f), m, SPARE, t) is None


@given(STATES, MEMBERS, DAYS, st.integers(1, 30))
def test_overdue_blocks(s, m, d, late):  # overdue-blocks
    base = clean(s, m)
    assert borrow(with_loan(base, Loan(SPARE + 1, m, d + late)), m, SPARE, d + late) is not None
    assert borrow(with_loan(base, Loan(SPARE + 1, m, d)), m, SPARE, d + late) is None


@given(STATES, MEMBERS, DAYS)
def test_held_copy(s, m, t):  # held-copy
    held = replace(clean(s, m), holds=((SPARE, other(m)),) + s.holds)
    assert borrow(held, m, SPARE, t) is None


@given(STATES, MEMBERS, DAYS)
def test_hold_ends(s, m, t):  # hold-ends
    after = borrow(replace(clean(s, m), holds=((SPARE, m),) + s.holds), m, SPARE, t)
    assert after is not None and (SPARE, m) not in after.holds


def test_periods():  # period-standard, period-premium
    assert PERIOD == {"standard": 14, "premium": 28}


@given(STATES, MEMBERS, DAYS)
def test_due_date(s, m, t):  # due-date
    base = clean(s, m)
    after = borrow(base, m, SPARE, t)
    assert after is not None and after.loan_of(SPARE).due == t + PERIOD[base.membership(m)]


@given(STATES, MEMBERS, DAYS, st.integers(0, MAX_RENEWALS - 1))
def test_renew_limits(s, m, d, r):  # renew-limits
    mine = with_loan(clean(s, m), Loan(SPARE, m, d, r))
    assert renew(mine, m, SPARE, d) is not None
    assert renew(with_loan(clean(s, m), Loan(SPARE, m, d, MAX_RENEWALS)), m, SPARE, d) is None
    assert renew(replace(mine, holds=((SPARE, other(m)),) + mine.holds), m, SPARE, d) is None


@given(STATES, MEMBERS, DAYS)
def test_renew_moves_due(s, m, d):  # renew-moves-due
    mine = with_loan(clean(s, m), Loan(SPARE, m, d))
    assert renew(mine, m, SPARE, d).loan_of(SPARE).due == d + PERIOD[s.membership(m)]


@given(STATES, MEMBERS, DAYS, st.integers(1, 30))
def test_renew_late(s, m, d, late):  # renew-late
    assert renew(with_loan(clean(s, m), Loan(SPARE, m, d)), m, SPARE, d + late) is None


@given(STATES, MEMBERS, DAYS)
def test_renew_borrower(s, m, d):  # renew-borrower
    assert renew(with_loan(clean(s, m), Loan(SPARE, other(m), d)), m, SPARE, d) is None


@given(STATES, MEMBERS, DAYS, st.integers(FINE_LIMIT, 50))
def test_renew_owing(s, m, d, f):  # renew-owing
    assert renew(with_loan(clean(s, m).with_fine(m, f), Loan(SPARE, m, d)), m, SPARE, d) is None


@given(STATES, COPIES, DAYS)
def test_return_ends(s, c, t):  # return-ends
    assert not give_back(s, c, t).on_loan(c)


@given(STATES, MEMBERS, DAYS, st.integers(0, 60))
def test_late_fine(s, m, d, late):  # late-fine
    lent = with_loan(s, Loan(SPARE, m, d))
    assert give_back(lent, SPARE, d + late).fine(m) == s.fine(m) + min(late, FINE_CAP)


@given(STATES, MEMBERS, DAYS, st.integers(FINE_CAP, 200))
def test_fine_cap(s, m, d, late):  # fine-cap
    lent = with_loan(s, Loan(SPARE, m, d))
    assert give_back(lent, SPARE, d + late).fine(m) == s.fine(m) + FINE_CAP


@given(STATES, MEMBERS, DAYS, st.integers(0, 30))
def test_on_time(s, m, d, early):  # on-time
    lent = with_loan(s, Loan(SPARE, m, d + early))
    assert give_back(lent, SPARE, d).fine(m) == s.fine(m)


@given(STATES, DAYS)
def test_return_unlent(s, t):  # return-unlent
    assert give_back(s, SPARE, t) == s


@given(STATES, MEMBERS)
def test_hold_lent(s, m):  # hold-lent
    assert place_hold(with_loan(clean(s, m), Loan(SPARE, other(m), FAR)), m, SPARE) is not None


@given(STATES, MEMBERS)
def test_hold_unlent(s, m):  # hold-unlent
    assert place_hold(clean(s, m), m, SPARE) is None


@given(STATES, MEMBERS)
def test_hold_own(s, m):  # hold-own
    assert place_hold(with_loan(clean(s, m), Loan(SPARE, m, FAR)), m, SPARE) is None


@given(STATES, MEMBERS)
def test_one_hold(s, m):  # one-hold
    lent = with_loan(clean(s, m), Loan(SPARE, other(m), FAR))
    held = replace(lent, holds=((SPARE, other(other(m))),) + lent.holds)
    assert place_hold(held, m, SPARE) is None
    after = place_hold(lent, m, SPARE)
    assert after is not None and sum(1 for h in after.holds if h[0] == SPARE) == 1


@given(STATES, MEMBERS)
def test_three_holds(s, m):  # three-holds
    base = premium(clean(s, m), m)
    for i in range(MAX_HOLDS + 1):
        base = with_loan(base, Loan(SPARE + 50 + i, other(m), FAR))
    for i in range(MAX_HOLDS - 1):
        base = replace(base, holds=((SPARE + 50 + i, m),) + base.holds)
    assert place_hold(base, m, SPARE + 50 + MAX_HOLDS - 1) is not None
    full = replace(base, holds=((SPARE + 50 + MAX_HOLDS - 1, m),) + base.holds)
    assert place_hold(full, m, SPARE + 50 + MAX_HOLDS) is None


@given(STATES, MEMBERS, st.integers(0, MAX_HOLDS - 1))
def test_hold_limit(s, m, held_count):  # hold-limit
    base = with_loan(standard(clean(s, m), m), Loan(SPARE, other(m), FAR))
    for i in range(held_count):
        copy = SPARE + 30 + i
        base = with_loan(base, Loan(copy, other(m), FAR))
        base = replace(base, holds=((copy, m),) + base.holds)
    assert place_hold(loans_of(base, m, MAX_LOANS - held_count - 1), m, SPARE) is not None
    assert place_hold(loans_of(base, m, MAX_LOANS - held_count), m, SPARE) is None


@given(STATES, MEMBERS, st.integers(0, 50))
def test_pay(s, m, a):  # pay
    assert pay(s, m, a).fine(m) == max(0, s.fine(m) - a)
