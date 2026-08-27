#!/usr/bin/env python3
"""Strict, solver-independent verifier for the six-string dual corpus.

In addition to checking every rational dual certificate, this version
mechanically verifies the full reverse-and-relabel reduction: involutivity,
orbit coverage, and exact invariance of every inequality row with its RHS,
every optimum-path equality, and the objective.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import gzip
import json
from pathlib import Path

import six_string_lp_model as model


EXPECTED_HEADER = {
    "format": "greedy-superstring-six-string-lp-duals-v1",
    "n": 6,
    "normalization": "OPT=1",
    "representative_greedy_orders": 60,
    "optimal_paths_per_order": 720,
    "certificate_count": 43200,
    "covered_case_count_by_involution": 86400,
}
EXPECTED_CERTIFICATE_KEYS = {"bound", "lo", "up", "y", "z"}


def new_variable_to_old_index():
    """Return the reverse-and-relabel variable permutation.

    Entry ``j`` is the old-system coordinate occupied by new coordinate
    ``j`` under l'_i=l_(5-i), w'_ij=w_(5-j,5-i).
    """
    mapping = []
    for i in model.VERTICES:
        mapping.append(model.L_INDEX[model.N - 1 - i])
    for i, j in model.DIRECTED_EDGES:
        mapping.append(model.W_INDEX[(model.N - 1 - j, model.N - 1 - i)])
    if sorted(mapping) != list(range(model.NVAR)):
        raise ValueError("symmetry variable map is not a permutation")
    if any(mapping[mapping[j]] != j for j in range(model.NVAR)):
        raise ValueError("symmetry variable map is not an involution")
    return tuple(mapping)


def map_new_row_to_old(row, mapping):
    if len(row) != model.NVAR:
        raise ValueError("row has unexpected dimension")
    result = [0] * model.NVAR
    for new_index, old_index in enumerate(mapping):
        result[old_index] = row[new_index]
    return result


def equality_for_path(path):
    """Build only the path-dependent normalization row."""
    equality = [0] * model.NVAR
    for i in model.VERTICES:
        equality[model.L_INDEX[i]] = 1
    for edge in zip(path[:-1], path[1:]):
        equality[model.W_INDEX[edge]] -= 1
    return equality


def verify_symmetry_reduction():
    """Check the exact LP isomorphism used to halve the case corpus."""
    mapping = new_variable_to_old_index()

    # Involutivity on the combinatorial objects, not merely on coordinates.
    for edge in model.DIRECTED_EDGES:
        if model.reverse_relabel_edge(model.reverse_relabel_edge(edge)) != edge:
            raise ValueError(f"edge transformation is not involutive: {edge}")
    for order in model.GREEDY_EDGE_ORDERS:
        transformed = model.reverse_relabel_order(order)
        if transformed not in model.GREEDY_EDGE_ORDERS:
            raise ValueError(f"order transformation is not closed: {order}")
        if model.reverse_relabel_order(transformed) != order:
            raise ValueError(f"order transformation is not involutive: {order}")
    for path in model.OPTIMAL_PATHS:
        transformed = model.reverse_relabel_path(path)
        if transformed not in model.OPTIMAL_PATHS:
            raise ValueError(f"path transformation is not closed: {path}")
        if model.reverse_relabel_path(transformed) != path:
            raise ValueError(f"path transformation is not involutive: {path}")

    representatives = set(model.REPRESENTATIVE_GREEDY_ORDERS)
    images = {model.reverse_relabel_order(order) for order in representatives}
    all_orders = set(model.GREEDY_EDGE_ORDERS)
    if len(representatives) != EXPECTED_HEADER["representative_greedy_orders"]:
        raise ValueError("unexpected number of symmetry representatives")
    if representatives & images:
        raise ValueError("symmetry representatives and their images intersect")
    if representatives | images != all_orders:
        raise ValueError("symmetry representatives do not cover every order")

    checked_equalities = 0
    checked_orders = 0
    probe_path = model.OPTIMAL_PATHS[0]
    for order in model.REPRESENTATIVE_GREEDY_ORDERS:
        reflected_order = model.reverse_relabel_order(order)
        old_rows, old_rhs, _, old_objective, _ = model.build_case(
            order, probe_path
        )
        new_rows, new_rhs, _, new_objective, _ = model.build_case(
            reflected_order, model.reverse_relabel_path(probe_path)
        )

        old_system = Counter(zip(map(tuple, old_rows), old_rhs))
        mapped_new_system = Counter(
            (tuple(map_new_row_to_old(row, mapping)), rhs)
            for row, rhs in zip(new_rows, new_rhs)
        )
        if mapped_new_system != old_system:
            missing = old_system - mapped_new_system
            extra = mapped_new_system - old_system
            raise ValueError(
                f"inequality/RHS multiset mismatch for order {order}; "
                f"missing={sum(missing.values())}, extra={sum(extra.values())}"
            )
        if map_new_row_to_old(new_objective, mapping) != old_objective:
            raise ValueError(f"objective mismatch for order {order}")

        for path in model.OPTIMAL_PATHS:
            reflected_path = model.reverse_relabel_path(path)
            old_equality = equality_for_path(path)
            new_equality = equality_for_path(reflected_path)
            if map_new_row_to_old(new_equality, mapping) != old_equality:
                raise ValueError(
                    f"equality mismatch for order {order}, path {path}"
                )
            checked_equalities += 1
        checked_orders += 1

    return {
        "variable_coordinates_checked": model.NVAR,
        "representative_orders_checked": checked_orders,
        "inequality_rhs_systems_checked": checked_orders,
        "objectives_checked": checked_orders,
        "path_equalities_checked": checked_equalities,
        "covered_greedy_orders": len(representatives | images),
    }


def decode_sparse(entries, size, sign, name):
    if not isinstance(entries, list):
        raise ValueError(f"{name} must be a list")
    result = []
    seen = set()
    for entry in entries:
        if not isinstance(entry, list) or len(entry) != 2:
            raise ValueError(f"malformed {name} entry {entry!r}")
        index, encoded = entry
        if not isinstance(index, int) or isinstance(index, bool):
            raise ValueError(f"noninteger {name} index {index!r}")
        if not 0 <= index < size:
            raise ValueError(f"{name} index {index!r} outside 0..{size - 1}")
        if index in seen:
            raise ValueError(f"duplicate {name} index {index}")
        seen.add(index)
        value = Fraction(encoded)
        if sign == "nonpositive" and value > 0:
            raise ValueError(f"positive {name} multiplier")
        if sign == "nonnegative" and value < 0:
            raise ValueError(f"negative {name} multiplier")
        if value:
            result.append((index, value))
    return result


def verify_certificate(certificate, rows, rhs, equality, objective):
    if not isinstance(certificate, dict):
        raise ValueError("certificate record is not an object")
    if set(certificate) != EXPECTED_CERTIFICATE_KEYS:
        raise ValueError(
            "certificate keys differ from the exact format: "
            f"{sorted(certificate)}"
        )
    y = decode_sparse(certificate["y"], len(rows), "nonpositive", "y")
    lower = decode_sparse(
        certificate["lo"], model.NVAR, "nonnegative", "lower"
    )
    upper = decode_sparse(
        certificate["up"], model.NVAR, "nonpositive", "upper"
    )
    if any(index >= model.N for index, _ in upper):
        raise ValueError("upper multiplier used on an unbounded overlap")
    z = Fraction(certificate["z"])

    stationarity = [z * equality[j] for j in range(model.NVAR)]
    for row_index, multiplier in y:
        for j, coefficient in enumerate(rows[row_index]):
            if coefficient:
                stationarity[j] += multiplier * coefficient
    for index, multiplier in lower:
        stationarity[index] += multiplier
    for index, multiplier in upper:
        stationarity[index] += multiplier
    exact_objective = [Fraction(value) for value in objective]
    if stationarity != exact_objective:
        bad = next(
            j
            for j, (actual, expected) in enumerate(
                zip(stationarity, exact_objective)
            )
            if actual != expected
        )
        raise ValueError(
            f"stationarity fails at variable {bad}: "
            f"{stationarity[bad]} != {exact_objective[bad]}"
        )

    dual_bound = sum(multiplier * rhs[index] for index, multiplier in y)
    dual_bound += z
    dual_bound += sum(multiplier for _, multiplier in upper)
    if dual_bound != Fraction(certificate["bound"]):
        raise ValueError("encoded dual bound is inconsistent")
    if dual_bound < -2:
        raise ValueError(f"dual bound {dual_bound} is below -2")
    support = len(y) + len(lower) + len(upper) + int(z != 0)
    return dual_bound, support


def verify(path):
    symmetry = verify_symmetry_reduction()
    expected_count = (
        len(model.REPRESENTATIVE_GREEDY_ORDERS) * len(model.OPTIMAL_PATHS)
    )
    weakest_bound = None
    maximum_support = 0
    count = 0
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        try:
            header = json.loads(next(stream))
        except StopIteration as error:
            raise ValueError("empty certificate stream") from error
        if header != EXPECTED_HEADER:
            raise ValueError(
                "certificate header differs from exact expected metadata: "
                f"{header!r}"
            )
        if expected_count != EXPECTED_HEADER["certificate_count"]:
            raise ValueError("model dimensions disagree with expected metadata")

        lines = iter(stream)
        for order_index, greedy_order in enumerate(
            model.REPRESENTATIVE_GREEDY_ORDERS
        ):
            rows, rhs, _, objective, _ = model.build_case(
                greedy_order, model.OPTIMAL_PATHS[0]
            )
            for path_index, optimal_path in enumerate(model.OPTIMAL_PATHS):
                try:
                    certificate = json.loads(next(lines))
                except StopIteration as error:
                    raise ValueError("certificate stream ended early") from error
                try:
                    dual_bound, support = verify_certificate(
                        certificate,
                        rows,
                        rhs,
                        equality_for_path(optimal_path),
                        objective,
                    )
                except Exception as error:
                    raise ValueError(
                        f"order {order_index}, path {path_index}: {error}"
                    ) from error
                count += 1
                weakest_bound = (
                    dual_bound
                    if weakest_bound is None
                    else min(weakest_bound, dual_bound)
                )
                maximum_support = max(maximum_support, support)
        try:
            next(lines)
        except StopIteration:
            pass
        else:
            raise ValueError("certificate stream has trailing records")

    return {
        "header_metadata_validated": EXPECTED_HEADER,
        "symmetry": symmetry,
        "verified_representative_cases": count,
        "covered_cases_by_involution": 2 * count,
        "weakest_dual_lower_bound": str(weakest_bound),
        "maximum_certificate_support": maximum_support,
        "conclusion": (
            "Every normalized six-string case has min(-greedy_length) >= -2; "
            "hence the necessary-condition LP has greedy_length <= 2*OPT."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate_file", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.certificate_file), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
