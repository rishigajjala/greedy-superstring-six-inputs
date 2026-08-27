#!/usr/bin/env python3
"""Generate gzip-compressed exact duals for all six-string LP cases.

Only one greedy order from each reverse-and-relabel orbit is generated.  The
involution has no fixed greedy orders at n=6, reducing 120*720 cases to
60*720=43,200.  HiGHS discovers duals; every dual is rationalized and checked
exactly before being written as one compact JSON object per gzip line.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

import six_string_lp_model as model


DENOMINATOR_LIMITS = (8, 16, 32, 64, 128, 256, 512, 1024, 4096, 16384)


def rationalize(value, denominator_limit):
    if abs(float(value)) < 1e-8:
        return Fraction(0)
    return Fraction(float(value)).limit_denominator(denominator_limit)


def sparse(values):
    return [[i, str(value)] for i, value in enumerate(values) if value]


def exact_certificate(result, rows, rhs, equality, objective):
    """Reconstruct and exactly validate a sparse rational LP dual."""
    for denominator_limit in DENOMINATOR_LIMITS:
        y = [rationalize(v, denominator_limit) for v in result.ineqlin.marginals]
        z = rationalize(result.eqlin.marginals[0], denominator_limit)
        lower = [rationalize(v, denominator_limit) for v in result.lower.marginals]
        upper = [rationalize(v, denominator_limit) for v in result.upper.marginals]
        y_sparse = [(i, value) for i, value in enumerate(y) if value]

        if not all(value <= 0 for _, value in y_sparse):
            continue
        if not all(value >= 0 for value in lower):
            continue
        if not all(value <= 0 for value in upper):
            continue
        if any(upper[model.N :]):
            continue

        stationarity = [
            z * equality[j] + lower[j] + upper[j]
            for j in range(model.NVAR)
        ]
        for row_index, multiplier in y_sparse:
            row = rows[row_index]
            for j, coefficient in enumerate(row):
                if coefficient:
                    stationarity[j] += multiplier * coefficient
        if stationarity != [Fraction(value) for value in objective]:
            continue

        dual_bound = sum(y[i] * rhs[i] for i, _ in y_sparse)
        dual_bound += z + sum(upper[: model.N])
        if dual_bound < -2:
            continue
        return {
            "y": sparse(y),
            "z": str(z),
            "lo": sparse(lower),
            "up": sparse(upper),
            "bound": str(dual_bound),
        }, denominator_limit
    raise RuntimeError("could not reconstruct an exact dual")


def generate(output):
    total = len(model.REPRESENTATIVE_GREEDY_ORDERS) * len(model.OPTIMAL_PATHS)
    header = {
        "format": "greedy-superstring-six-string-lp-duals-v1",
        "n": model.N,
        "normalization": "OPT=1",
        "representative_greedy_orders": len(model.REPRESENTATIVE_GREEDY_ORDERS),
        "optimal_paths_per_order": len(model.OPTIMAL_PATHS),
        "certificate_count": total,
        "covered_case_count_by_involution": 2 * total,
    }
    maximum_ratio = float("-inf")
    maximum_support = 0
    maximum_denominator_limit = 1

    with gzip.open(output, "wt", encoding="utf-8", compresslevel=9) as stream:
        stream.write(json.dumps(header, separators=(",", ":")) + "\n")
        case_index = 0
        for order_index, greedy_order in enumerate(
            model.REPRESENTATIVE_GREEDY_ORDERS
        ):
            for path_index, optimal_path in enumerate(model.OPTIMAL_PATHS):
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
                        f"LP failed at order {order_index}, path {path_index}: "
                        f"{result.message}"
                    )
                certificate, used_limit = exact_certificate(
                    result, rows, rhs, equality, objective
                )
                stream.write(json.dumps(certificate, separators=(",", ":")) + "\n")

                case_index += 1
                maximum_ratio = max(maximum_ratio, -float(result.fun))
                support = (
                    len(certificate["y"])
                    + int(certificate["z"] != "0")
                    + len(certificate["lo"])
                    + len(certificate["up"])
                )
                maximum_support = max(maximum_support, support)
                maximum_denominator_limit = max(
                    maximum_denominator_limit, used_limit
                )
                if case_index % 720 == 0:
                    print(
                        f"generated {case_index}/{total}; "
                        f"max ratio {maximum_ratio:.12g}",
                        flush=True,
                    )

    summary = {
        **header,
        "maximum_numerical_ratio": maximum_ratio,
        "maximum_certificate_support": maximum_support,
        "maximum_denominator_limit_used": maximum_denominator_limit,
        "output": str(output),
    }
    return summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("six_string_certificates.jsonl.gz"),
    )
    parser.add_argument("--summary", type=Path)
    args = parser.parse_args()
    summary = generate(args.output)
    rendered = json.dumps(summary, indent=2, sort_keys=True)
    print(rendered)
    if args.summary:
        args.summary.write_text(rendered + "\n")


if __name__ == "__main__":
    main()

