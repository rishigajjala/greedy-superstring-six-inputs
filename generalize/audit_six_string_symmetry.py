#!/usr/bin/env python3
"""Mechanically verify the reverse-and-relabel LP symmetry exactly."""

from __future__ import annotations

from collections import Counter
import json

import six_string_lp_model as model


def new_variable_to_old_index():
    mapping = []
    for i in model.VERTICES:
        mapping.append(model.L_INDEX[model.N - 1 - i])
    for i, j in model.DIRECTED_EDGES:
        old_edge = (model.N - 1 - j, model.N - 1 - i)
        mapping.append(model.W_INDEX[old_edge])
    assert len(mapping) == model.NVAR
    assert set(mapping) == set(range(model.NVAR))
    return mapping


def map_new_row_to_old(row, mapping):
    result = [0] * model.NVAR
    for new_index, old_index in enumerate(mapping):
        result[old_index] = row[new_index]
    return result


def audit():
    mapping = new_variable_to_old_index()
    checked_orders = 0
    checked_path_equalities = 0
    for order in model.REPRESENTATIVE_GREEDY_ORDERS:
        reflected_order = model.reverse_relabel_order(order)
        old_rows, old_rhs, _, old_objective, _ = model.build_case(
            order, model.OPTIMAL_PATHS[0]
        )
        new_rows, new_rhs, _, new_objective, _ = model.build_case(
            reflected_order, model.OPTIMAL_PATHS[0]
        )
        old_system = Counter(zip(map(tuple, old_rows), old_rhs))
        mapped_new_system = Counter(
            (tuple(map_new_row_to_old(row, mapping)), rhs)
            for row, rhs in zip(new_rows, new_rhs)
        )
        if old_system != mapped_new_system:
            raise ValueError(f"inequality system mismatch for order {order}")
        if map_new_row_to_old(new_objective, mapping) != old_objective:
            raise ValueError(f"objective mismatch for order {order}")
        checked_orders += 1

        for path in model.OPTIMAL_PATHS:
            reflected_path = model.reverse_relabel_path(path)
            _, _, old_equality, _, _ = model.build_case(order, path)
            _, _, new_equality, _, _ = model.build_case(
                reflected_order, reflected_path
            )
            if map_new_row_to_old(new_equality, mapping) != old_equality:
                raise ValueError(
                    f"equality mismatch for order {order}, path {path}"
                )
            checked_path_equalities += 1

    representatives = set(model.REPRESENTATIVE_GREEDY_ORDERS)
    images = {model.reverse_relabel_order(order) for order in representatives}
    if representatives & images:
        raise ValueError("symmetry has a fixed representative order")
    if representatives | images != set(model.GREEDY_EDGE_ORDERS):
        raise ValueError("symmetry orbits do not cover every greedy order")
    return {
        "representative_orders_checked": checked_orders,
        "inequality_systems_checked": checked_orders,
        "objectives_checked": checked_orders,
        "path_equalities_checked": checked_path_equalities,
        "covered_greedy_orders": len(representatives | images),
        "conclusion": (
            "The reverse-and-relabel variable permutation maps every representative "
            "LP exactly to its partner and covers all 120 greedy orders."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
