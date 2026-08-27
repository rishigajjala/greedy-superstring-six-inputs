#!/usr/bin/env python3
"""Check the asymptotically sharp five-string family from FIVE_STRING_PROOF.md."""

from __future__ import annotations

import argparse
from itertools import permutations


def overlap(left: str, right: str) -> int:
    for size in range(min(len(left), len(right)), -1, -1):
        if size == 0 or left[-size:] == right[:size]:
            return size
    raise AssertionError("unreachable")


def merge(left: str, right: str) -> str:
    return left + right[overlap(left, right) :]


def family(t: int) -> dict[str, str]:
    return {
        "A": "001",
        "B": "0" + "1" * (t - 1),
        "C": "101",
        "D": "1" * (t - 1) + "0",
        "E": "1" * t,
    }


def check(t: int) -> dict[str, int]:
    words = family(t)
    if any(
        words[x] in words[y]
        for x in words
        for y in words
        if x != y
    ):
        raise AssertionError(f"family is not reduced at t={t}")

    current = dict(words)
    run = [("B", "D", "BD"), ("C", "BD", "CBD"),
           ("A", "CBD", "ACBD"), ("E", "ACBD", "G")]
    savings = 0
    for left, right, name in run:
        chosen = overlap(current[left], current[right])
        maximum = max(
            overlap(current[x], current[y])
            for x in current
            for y in current
            if x != y
        )
        if chosen != maximum:
            raise AssertionError(
                f"illegal greedy step at t={t}: {left}->{right}, "
                f"chosen={chosen}, maximum={maximum}"
            )
        savings += chosen
        current[name] = merge(current.pop(left), current.pop(right))

    greedy = len(current["G"])
    optimum = min(
        sum(len(words[name]) for name in order)
        - sum(overlap(words[x], words[y]) for x, y in zip(order, order[1:]))
        for order in permutations(words)
    )
    expected = {"greedy": 2 * t + 4, "optimum": t + 4, "savings": t + 2}
    actual = {"greedy": greedy, "optimum": optimum, "savings": savings}
    if actual != expected:
        raise AssertionError(f"t={t}: {actual=} != {expected=}")
    return actual


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-t", type=int, default=100)
    args = parser.parse_args()
    if args.max_t < 3:
        parser.error("--max-t must be at least 3")
    for t in range(3, args.max_t + 1):
        check(t)
    print(
        f"verified t=3..{args.max_t}; "
        "G_t=2t+4, OPT_t=t+4, and every prescribed merge is greedy"
    )


if __name__ == "__main__":
    main()
