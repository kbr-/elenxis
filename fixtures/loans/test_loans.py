"""Property tests of loans.py, one or more per clause of loans.md, named by the ledger row they cover.

The domain: states built by applying random requests to an empty library of copies 0 to 9 and
members 0 to 4 (member 4 premium), so every state is one the library can reach.
"""

from __future__ import annotations

from hypothesis import given, settings, strategies as st

settings.register_profile("fixture", database=None)
settings.load_profile("fixture")

from loans import (FINE_LIMIT, MAX_LOANS, MAX_RENEWALS, PERIOD, State, borrow, give_back, pay,
                   place_hold, renew)

COPIES = st.integers(0, 9)
MEMBERS = st.integers(0, 4)
DAYS = st.integers(0, 120)
# Borrowing weighted, and member 0 favoured, so one member reaches the five-loan limit.
REQUEST = st.tuples(st.sampled_from(["borrow"] * 4 + ["renew", "return", "hold", "pay"]),
                    st.one_of(st.just(0), MEMBERS), COPIES, st.integers(0, 20))


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


@given(STATES, MEMBERS, COPIES, DAYS)
def test_borrow_free(s, m, c, t):  # borrow-free
    if not s.on_loan(c) and s.count(m) < MAX_LOANS and s.fine(m) < FINE_LIMIT and not s.held_by_other(c, m):
        assert borrow(s, m, c, t) is not None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_never_two_borrowers(s, m, c, t):  # never-two-borrowers
    if s.on_loan(c):
        assert borrow(s, m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_five_copies(s, m, c, t):  # five-copies
    after = borrow(s, m, c, t)
    if s.count(m) >= MAX_LOANS:
        assert after is None
    if after is not None:
        assert after.count(m) <= MAX_LOANS


@given(STATES, MEMBERS, COPIES, DAYS)
def test_fines_block(s, m, c, t):  # fines-block
    if s.fine(m) >= FINE_LIMIT:
        assert borrow(s, m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_held_copy(s, m, c, t):  # held-copy
    if s.held_by_other(c, m):
        assert borrow(s, m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_hold_ends(s, m, c, t):  # hold-ends
    after = borrow(s, m, c, t)
    if after is not None:
        assert (c, m) not in after.holds


def test_periods():  # period-standard, period-premium
    assert PERIOD == {"standard": 14, "premium": 28}


@given(STATES, MEMBERS, COPIES, DAYS)
def test_due_date(s, m, c, t):  # due-date
    after = borrow(s, m, c, t)
    if after is not None:
        assert after.loan_of(c).due == t + PERIOD[s.membership(m)]


@given(STATES, MEMBERS, COPIES, DAYS)
def test_renew_limits(s, m, c, t):  # renew-limits
    loan = s.loan_of(c)
    if loan is not None and (loan.renewals >= MAX_RENEWALS or s.held_by_other(c, m)):
        assert renew(s, m, c, t) is None


@given(STATES, MEMBERS, COPIES, DAYS)
def test_renew_moves_due(s, m, c, t):  # renew-moves-due
    after = renew(s, m, c, t)
    if after is not None:
        assert after.loan_of(c).due == s.loan_of(c).due + PERIOD[s.membership(m)]


@given(STATES, MEMBERS, COPIES, DAYS)
def test_renew_late(s, m, c, t):  # renew-late
    loan = s.loan_of(c)
    if loan is not None and loan.due < t:
        assert renew(s, m, c, t) is None


@given(STATES, COPIES, DAYS)
def test_return_ends(s, c, t):  # return-ends
    assert not give_back(s, c, t).on_loan(c)


@given(STATES, COPIES, DAYS)
def test_late_fine(s, c, t):  # late-fine
    loan = s.loan_of(c)
    if loan is not None:
        assert give_back(s, c, t).fine(loan.member) == s.fine(loan.member) + max(0, t - loan.due)


@given(STATES, COPIES, DAYS)
def test_on_time(s, c, t):  # on-time
    loan = s.loan_of(c)
    if loan is not None and t <= loan.due:
        assert give_back(s, c, t).fine(loan.member) == s.fine(loan.member)


@given(STATES, COPIES, DAYS)
def test_return_unlent(s, c, t):  # return-unlent
    if s.loan_of(c) is None:
        assert give_back(s, c, t) == s


@given(STATES, MEMBERS, COPIES)
def test_hold_lent(s, m, c):  # hold-lent
    if (s.on_loan(c) and not any(x.copy == c and x.member == m for x in s.loans)
            and not any(h[0] == c for h in s.holds)):
        assert place_hold(s, m, c) is not None


@given(STATES, MEMBERS, COPIES)
def test_hold_own(s, m, c):  # hold-own
    if any(x.copy == c and x.member == m for x in s.loans):
        assert place_hold(s, m, c) is None


@given(STATES, MEMBERS, COPIES)
def test_one_hold(s, m, c):  # one-hold
    if any(h[0] == c for h in s.holds):
        assert place_hold(s, m, c) is None
    after = place_hold(s, m, c)
    if after is not None:
        assert sum(1 for h in after.holds if h[0] == c) == 1


@given(STATES, MEMBERS, st.integers(0, 50))
def test_pay(s, m, a):  # pay
    assert pay(s, m, a).fine(m) == max(0, s.fine(m) - a)


def test_generator_reaches_every_precondition():
    """The states reach each case the properties condition on, so none of them holds vacuously."""
    from hypothesis import find
    find(STATES, lambda s: any(s.fine(m) >= FINE_LIMIT for m in range(5)))
    find(STATES, lambda s: any(s.count(m) >= MAX_LOANS for m in range(5)))
    find(STATES, lambda s: any(x.renewals >= MAX_RENEWALS for x in s.loans))
    find(STATES, lambda s: any(s.held_by_other(c, m) for c in range(10) for m in range(5)
                               if s.on_loan(c)))
    find(STATES, lambda s: any(x.member == 4 for x in s.loans))


@settings(max_examples=50)
@given(STATES, MEMBERS, COPIES, DAYS)
def test_refusal(s, m, c, t):  # refusal
    for result in (borrow(s, m, c, t), renew(s, m, c, t), place_hold(s, m, c)):
        assert result is None or isinstance(result, State)
