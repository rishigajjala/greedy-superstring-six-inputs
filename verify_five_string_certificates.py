#!/usr/bin/env python3
"""Verify all five-string dual certificates using exact rational arithmetic.

This verifier uses only Python's standard library.  It never calls an LP solver.
For each of 24 greedy edge orders and 120 optimal string orders, it checks dual
signs, coefficient stationarity, and a dual lower bound of at least -2.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

import five_string_lp_model as model


EXPECTED_FORMAT = "greedy-superstring-five-string-lp-duals-v1"


def dense_sparse(entries, size):
    result = [Fraction(0)] * size
    seen = set()
    for index, value in entries:
        if not isinstance(index, int) or not 0 <= index < size:
            raise ValueError(f"sparse index {index!r} outside 0..{size - 1}")
        if index in seen:
            raise ValueError(f"duplicate sparse index {index}")
        seen.add(index)
        result[index] = Fraction(value)
    return result


def verify_one(certificate, greedy_order, optimal_path):
    encoded_order = [
        model.GREEDY_PATH_EDGES.index(edge) for edge in greedy_order
    ]
    if certificate["greedy_edge_order"] != encoded_order:
        raise ValueError("certificate greedy order does not match case order")
    if certificate["optimal_path"] != list(optimal_path):
        raise ValueError("certificate optimal path does not match case order")

    rows, rhs, equality, objective, _ = model.build_case(
        greedy_order, optimal_path
    )
    y = dense_sparse(
        certificate["inequality_multipliers"], len(rows)
    )
    z = Fraction(certificate["equality_multiplier"])
    lower = dense_sparse(
        certificate["lower_bound_multipliers"], model.NVAR
    )
    upper = dense_sparse(
        certificate["upper_bound_multipliers"], model.NVAR
    )

    if not all(value <= 0 for value in y):
        raise ValueError("an A*x<=b multiplier is positive")
    if not all(value >= 0 for value in lower):
        raise ValueError("a lower-bound multiplier is negative")
    if not all(value <= 0 for value in upper):
        raise ValueError("an upper-bound multiplier is positive")
    if any(upper[index] for index in range(model.N, model.NVAR)):
        raise ValueError("a variable without a finite upper bound is used")

    for variable in range(model.NVAR):
        coefficient = sum(
            y[index] * rows[index][variable]
            for index in range(len(rows))
        )
        coefficient += z * equality[variable]
        coefficient += lower[variable] + upper[variable]
        if coefficient != objective[variable]:
            raise ValueError(
                f"stationarity fails at variable {variable}: "
                f"{coefficient} != {objective[variable]}"
            )

    dual_bound = sum(
        y[index] * rhs[index] for index in range(len(rows))
    )
    dual_bound += z
    dual_bound += sum(upper[index] for index in range(model.N))
    claimed_bound = Fraction(certificate["dual_lower_bound"])
    if dual_bound != claimed_bound:
        raise ValueError(
            f"dual bound mismatch: {dual_bound} != {claimed_bound}"
        )
    if dual_bound < -2:
        raise ValueError(f"dual lower bound {dual_bound} is below -2")

    support = (
        sum(value != 0 for value in y)
        + int(z != 0)
        + sum(value != 0 for value in lower)
        + sum(value != 0 for value in upper)
    )
    return dual_bound, support


def verify(payload):
    if payload.get("format") != EXPECTED_FORMAT:
        raise ValueError("unexpected certificate format")

    expected_cases = [
        (greedy_order, optimal_path)
        for greedy_order in model.GREEDY_EDGE_ORDERS
        for optimal_path in model.OPTIMAL_PATHS
    ]
    certificates = payload.get("certificates")
    if not isinstance(certificates, list):
        raise ValueError("certificates must be a list")
    if len(certificates) != len(expected_cases):
        raise ValueError(
            f"expected {len(expected_cases)} cases, got {len(certificates)}"
        )
    if payload.get("case_count") != len(expected_cases):
        raise ValueError("case_count metadata is inconsistent")

    weakest_bound = None
    maximum_support = 0
    for case_number, (certificate, case) in enumerate(
        zip(certificates, expected_cases), start=1
    ):
        try:
            dual_bound, support = verify_one(certificate, *case)
        except Exception as error:
            raise ValueError(f"case {case_number}: {error}") from error
        if weakest_bound is None or dual_bound < weakest_bound:
            weakest_bound = dual_bound
        maximum_support = max(maximum_support, support)

    return {
        "verified_cases": len(expected_cases),
        "weakest_dual_lower_bound": str(weakest_bound),
        "maximum_certificate_support": maximum_support,
        "conclusion": (
            "For every enumerated case, min(-greedy_length) >= -2 under "
            "OPT=1; hence greedy_length <= 2*OPT in the relaxation."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate_file", type=Path)
    args = parser.parse_args()
    payload = json.loads(args.certificate_file.read_text())
    print(json.dumps(verify(payload), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
