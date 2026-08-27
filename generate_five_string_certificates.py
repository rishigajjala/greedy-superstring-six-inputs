#!/usr/bin/env python3
"""Generate exact rational dual certificates for all five-string LP cases.

SciPy/HiGHS is used only to discover sparse dual solutions.  Every floating
solution is reconstructed as small rational numbers and checked exactly before
it is written.  The separate verifier needs only Python's standard library.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

import five_string_lp_model as model


DENOMINATOR_LIMITS = (8, 16, 32, 64, 128, 256, 512, 1024, 4096)


def rationalize(value, denominator_limit):
    if abs(float(value)) < 1e-8:
        return Fraction(0)
    return Fraction(float(value)).limit_denominator(denominator_limit)


def sparse(values):
    return [
        [index, str(value)]
        for index, value in enumerate(values)
        if value
    ]


def exact_certificate(result, rows, rhs, equality, objective):
    """Reconstruct a valid exact dual certificate from HiGHS marginals."""
    for denominator_limit in DENOMINATOR_LIMITS:
        y = [
            rationalize(value, denominator_limit)
            for value in result.ineqlin.marginals
        ]
        z = rationalize(result.eqlin.marginals[0], denominator_limit)
        lower = [
            rationalize(value, denominator_limit)
            for value in result.lower.marginals
        ]
        upper = [
            rationalize(value, denominator_limit)
            for value in result.upper.marginals
        ]

        if not all(value <= 0 for value in y):
            continue
        if not all(value >= 0 for value in lower):
            continue
        if not all(value <= 0 for value in upper):
            continue
        if any(upper[index] for index in range(model.N, model.NVAR)):
            continue

        stationarity = []
        for variable in range(model.NVAR):
            value = sum(
                y[index] * rows[index][variable]
                for index in range(len(rows))
            )
            value += z * equality[variable]
            value += lower[variable] + upper[variable]
            stationarity.append(value)

        if stationarity != [Fraction(value) for value in objective]:
            continue

        dual_bound = sum(
            y[index] * rhs[index] for index in range(len(rows))
        )
        dual_bound += z
        dual_bound += sum(upper[index] for index in range(model.N))
        if dual_bound < -2:
            continue

        return {
            "inequality_multipliers": sparse(y),
            "equality_multiplier": str(z),
            "lower_bound_multipliers": sparse(lower),
            "upper_bound_multipliers": sparse(upper),
            "dual_lower_bound": str(dual_bound),
        }

    raise RuntimeError("could not reconstruct an exact dual certificate")


def generate():
    certificates = []
    total = len(model.GREEDY_EDGE_ORDERS) * len(model.OPTIMAL_PATHS)
    maximum_relaxed_ratio = float("-inf")
    maximum_support = 0
    maximum_denominator = 1

    for case_index, (greedy_order, optimal_path) in enumerate(
        (
            (greedy_order, optimal_path)
            for greedy_order in model.GREEDY_EDGE_ORDERS
            for optimal_path in model.OPTIMAL_PATHS
        ),
        start=1,
    ):
        rows, rhs, equality, objective, _ = model.build_case(
            greedy_order, optimal_path
        )
        result = linprog(
            np.asarray(objective, dtype=float),
            A_ub=np.asarray(rows, dtype=float),
            b_ub=np.asarray(rhs, dtype=float),
            A_eq=np.asarray([equality], dtype=float),
            b_eq=np.asarray([1.0]),
            bounds=[(0.0, 1.0)] * model.N
            + [(0.0, None)] * len(model.DIRECTED_EDGES),
            method="highs",
        )
        if not result.success:
            raise RuntimeError(
                f"LP case {case_index} failed: {result.message}"
            )

        certificate = exact_certificate(
            result, rows, rhs, equality, objective
        )
        certificate["greedy_edge_order"] = [
            model.GREEDY_PATH_EDGES.index(edge) for edge in greedy_order
        ]
        certificate["optimal_path"] = list(optimal_path)
        certificates.append(certificate)

        maximum_relaxed_ratio = max(
            maximum_relaxed_ratio, -float(result.fun)
        )
        all_values = []
        for key in (
            "inequality_multipliers",
            "lower_bound_multipliers",
            "upper_bound_multipliers",
        ):
            all_values.extend(Fraction(value) for _, value in certificate[key])
        all_values.append(Fraction(certificate["equality_multiplier"]))
        maximum_support = max(
            maximum_support,
            sum(value != 0 for value in all_values),
        )
        maximum_denominator = max(
            maximum_denominator,
            *(value.denominator for value in all_values),
        )

        if case_index % 240 == 0:
            print(f"generated {case_index}/{total}", flush=True)

    return {
        "format": "greedy-superstring-five-string-lp-duals-v1",
        "case_count": len(certificates),
        "normalization": "OPT = 1",
        "maximum_numerical_relaxed_ratio": maximum_relaxed_ratio,
        "maximum_certificate_support": maximum_support,
        "maximum_certificate_denominator": maximum_denominator,
        "certificates": certificates,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("five_string_certificates.json"),
    )
    args = parser.parse_args()
    payload = generate()
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )
    print(
        f"wrote {payload['case_count']} exact certificates to {args.output}"
    )


if __name__ == "__main__":
    main()
