# SPDX-License-Identifier: Apache-2.0
# CONFESSION: JSON transport for the existing synthetic fixture's Python operations.
"""Run the loans fixture's operations in order and return every observed state."""

from __future__ import annotations

from dataclasses import asdict
import json
from pathlib import Path
import sys
from typing import TypedDict, cast


class LoanData(TypedDict):
    copy: int
    member: int
    due: int
    renewals: int


class StateData(TypedDict):
    loans: list[LoanData]
    holds: list[tuple[int, int]]
    fines: list[tuple[int, int]]
    premium: list[int]


class Operation(TypedDict, total=False):
    kind: str
    member: int
    copy: int
    today: int
    amount: int


class Request(TypedDict):
    initial: StateData
    operations: list[Operation]


def main() -> None:
    sys.path.insert(0, str(Path.cwd()))
    from loans import Loan, State, borrow, give_back, pay, place_hold, renew

    request = cast(Request, json.loads(Path(sys.argv[1]).read_text()))
    initial = request["initial"]
    state = State(
        loans=tuple(Loan(**item) for item in initial["loans"]),
        holds=tuple((copy, member) for copy, member in initial["holds"]),
        fines=tuple((member, amount) for member, amount in initial["fines"]),
        premium=frozenset(initial["premium"]),
    )
    observations = []
    for op in request["operations"]:
        match op["kind"]:
            case "borrow":
                result = borrow(state, op["member"], op["copy"], op["today"])
            case "renew":
                result = renew(state, op["member"], op["copy"], op["today"])
            case "return":
                result = give_back(state, op["copy"], op["today"])
            case "hold":
                result = place_hold(state, op["member"], op["copy"])
            case "pay":
                result = pay(state, op["member"], op["amount"])
            case kind:
                raise ValueError(f"unknown replay operation: {kind}")
        accepted = result is not None
        if result is not None:
            state = result
        snapshot = {
            "loans": [asdict(loan) for loan in state.loans],
            "holds": state.holds,
            "fines": sorted(state.fines),
            "premium": sorted(state.premium),
        }
        observations.append({"accepted": accepted, "state": snapshot})
    print(json.dumps(observations))


if __name__ == "__main__":
    main()
