#!/usr/bin/env python3
"""Pure-integer model for the six-string necessary-condition LP.

This module has no solver dependency.  It is shared by the certificate
generator and the exact rational verifier.
"""

from __future__ import annotations

import itertools


N = 6
VERTICES = tuple(range(N))
DIRECTED_EDGES = tuple(
    (i, j) for i in VERTICES for j in VERTICES if i != j
)
L_INDEX = {i: i for i in VERTICES}
W_INDEX = {edge: N + k for k, edge in enumerate(DIRECTED_EDGES)}
NVAR = N + len(DIRECTED_EDGES)
GREEDY_PATH_EDGES = tuple((i, i + 1) for i in range(N - 1))
GREEDY_EDGE_ORDERS = tuple(itertools.permutations(GREEDY_PATH_EDGES))
OPTIMAL_PATHS = tuple(itertools.permutations(VERTICES))


def zero_row():
    return [0] * NVAR


def feasible_edges(chosen):
    """Edges that can still extend to a directed Hamiltonian path."""
    outgoing_used = {i for i, _ in chosen}
    incoming_used = {j for _, j in chosen}
    parent = list(VERTICES)

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        x, y = find(x), find(y)
        if x != y:
            parent[y] = x

    for i, j in chosen:
        union(i, j)

    return tuple(
        (i, j)
        for i, j in DIRECTED_EDGES
        if i not in outgoing_used
        and j not in incoming_used
        and find(i) != find(j)
    )


def build_case(greedy_edge_order, optimal_path, include_labels=False):
    """Return integer ``(A,b,e,c,labels)`` for ``min c*x``.

    Feasible points satisfy ``A*x <= b``, ``e*x = 1``, nonnegativity,
    and ``l_i <= 1``.  The equality normalizes the nominated optimum-path
    length to one.  The objective is minus the greedy-output length.
    """
    rows = []
    rhs = []
    labels = []

    def append(row, bound, label):
        rows.append(row)
        rhs.append(bound)
        if include_labels:
            labels.append(label)

    # Endpoint caps.
    for i, j in DIRECTED_EDGES:
        for endpoint in (i, j):
            row = zero_row()
            row[W_INDEX[(i, j)]] = 1
            row[L_INDEX[endpoint]] = -1
            append(row, 0, f"cap w{i}{j} <= l{endpoint}")

    # Directed overlap-distance triangle inequalities.
    for i, j, k in itertools.permutations(VERTICES, 3):
        row = zero_row()
        row[W_INDEX[(i, j)]] = 1
        row[W_INDEX[(j, k)]] = 1
        row[W_INDEX[(i, k)]] = -1
        row[L_INDEX[j]] = -1
        append(row, 0, f"triangle {i}->{j}->{k}")

    # Global interval-pair inequalities, with OPT normalized to one.
    for i, j in itertools.combinations(VERTICES, 2):
        row = zero_row()
        row[L_INDEX[i]] = 1
        row[L_INDEX[j]] = 1
        row[W_INDEX[(i, j)]] = -1
        row[W_INDEX[(j, i)]] = -1
        append(row, 1, f"interval pair {i},{j}")

    # Greedy feasibility/dominance and every licensed conditional Monge row.
    chosen = ()
    for step, selected in enumerate(greedy_edge_order):
        feasible = feasible_edges(chosen)
        feasible_set = set(feasible)
        if selected not in feasible_set:
            raise ValueError(f"edge {selected} infeasible at greedy step {step}")
        u, v = selected
        for candidate in feasible:
            if candidate == selected:
                continue
            row = zero_row()
            row[W_INDEX[candidate]] += 1
            row[W_INDEX[selected]] -= 1
            append(row, 0, f"greedy {step}: {selected} >= {candidate}")

        for u_prime in VERTICES:
            for v_prime in VERTICES:
                cross_a = (u, v_prime)
                cross_b = (u_prime, v)
                bottom = (u_prime, v_prime)
                four = (selected, cross_a, cross_b, bottom)
                if any(i == j for i, j in four):
                    continue
                if cross_a not in feasible_set or cross_b not in feasible_set:
                    continue
                row = zero_row()
                row[W_INDEX[cross_a]] += 1
                row[W_INDEX[cross_b]] += 1
                row[W_INDEX[selected]] -= 1
                row[W_INDEX[bottom]] -= 1
                append(
                    row,
                    0,
                    f"Monge {step}: {selected}; {cross_a},{cross_b}; {bottom}",
                )
        chosen += (selected,)

    equality = zero_row()
    for i in VERTICES:
        equality[L_INDEX[i]] = 1
    for edge in zip(optimal_path[:-1], optimal_path[1:]):
        equality[W_INDEX[edge]] -= 1

    objective = zero_row()
    for i in VERTICES:
        objective[L_INDEX[i]] = -1
    for edge in GREEDY_PATH_EDGES:
        objective[W_INDEX[edge]] += 1

    return rows, rhs, equality, objective, labels


def reverse_relabel_edge(edge):
    """Reverse strings and relabel i as N-1-i, preserving the greedy path."""
    i, j = edge
    return N - 1 - j, N - 1 - i


def reverse_relabel_order(order):
    return tuple(reverse_relabel_edge(edge) for edge in order)


def reverse_relabel_path(path):
    return tuple(N - 1 - i for i in reversed(path))


REPRESENTATIVE_GREEDY_ORDERS = tuple(
    order
    for order in GREEDY_EDGE_ORDERS
    if order < reverse_relabel_order(order)
)

