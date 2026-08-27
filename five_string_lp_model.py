#!/usr/bin/env python3
"""Exact integer LP model for the five-input greedy-superstring theorem.

This module only builds constraints.  It does not solve an LP and has no
third-party dependencies, so the exact certificate verifier can import it.
"""

from __future__ import annotations

import itertools


N = 5
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
    """Original overlap-graph edges still extendible to a Hamilton path."""
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


def build_case(greedy_edge_order, optimal_path):
    """Return integer (A, b, e, c, labels) for min c*x.

    Feasible points satisfy A*x <= b, e*x = 1, all variables >= 0,
    and the five length variables <= 1.  Here OPT is normalized to 1,
    c*x is minus the greedy-output length, and a dual lower bound of -2
    proves the desired ratio.
    """
    rows = []
    rhs = []
    labels = []

    # Directed overlaps do not exceed either endpoint string length.
    for i, j in DIRECTED_EDGES:
        for endpoint in (i, j):
            row = zero_row()
            row[W_INDEX[(i, j)]] = 1
            row[L_INDEX[endpoint]] = -1
            rows.append(row)
            rhs.append(0)
            labels.append(f"cap w{i}{j} <= l{endpoint}")

    # Directed overlap-distance triangle inequality.
    for i, j, k in itertools.permutations(VERTICES, 3):
        row = zero_row()
        row[W_INDEX[(i, j)]] = 1
        row[W_INDEX[(j, k)]] = 1
        row[W_INDEX[(i, k)]] = -1
        row[L_INDEX[j]] = -1
        rows.append(row)
        rhs.append(0)
        labels.append(f"triangle {i}->{j}->{k}")

    # Weakened interval inequality:
    # max(w_ij,w_ji) >= l_i+l_j-OPT implies the sum version below.
    for i, j in itertools.combinations(VERTICES, 2):
        row = zero_row()
        row[L_INDEX[i]] = 1
        row[L_INDEX[j]] = 1
        row[W_INDEX[(i, j)]] = -1
        row[W_INDEX[(j, i)]] = -1
        rows.append(row)
        rhs.append(1)
        labels.append(f"interval pair {i},{j}")

    # Greedy dominance and each licensed conditional-Monge rectangle.
    chosen = ()
    for selected in greedy_edge_order:
        feasible = feasible_edges(chosen)
        feasible_set = set(feasible)
        u, v = selected

        for candidate in feasible:
            if candidate == selected:
                continue
            row = zero_row()
            row[W_INDEX[candidate]] = 1
            row[W_INDEX[selected]] -= 1
            rows.append(row)
            rhs.append(0)
            labels.append(f"greedy {selected} >= {candidate}")

        for u_prime in VERTICES:
            for v_prime in VERTICES:
                cross_a = (u, v_prime)
                cross_b = (u_prime, v)
                bottom = (u_prime, v_prime)
                four = (selected, cross_a, cross_b, bottom)
                if any(i == j for i, j in four):
                    continue
                if (
                    cross_a not in feasible_set
                    or cross_b not in feasible_set
                ):
                    continue
                row = zero_row()
                row[W_INDEX[cross_a]] += 1
                row[W_INDEX[cross_b]] += 1
                row[W_INDEX[selected]] -= 1
                row[W_INDEX[bottom]] -= 1
                rows.append(row)
                rhs.append(0)
                labels.append(
                    f"Monge {selected}; {cross_a}, {cross_b}; {bottom}"
                )

        chosen += (selected,)

    # The nominated order realizes an optimum of normalized length one.
    equality = zero_row()
    for i in VERTICES:
        equality[L_INDEX[i]] = 1
    for edge in zip(optimal_path[:-1], optimal_path[1:]):
        equality[W_INDEX[edge]] -= 1

    # Minimize minus the length of the relabeled greedy path 0->1->...->4.
    objective = zero_row()
    for i in VERTICES:
        objective[L_INDEX[i]] = -1
    for edge in GREEDY_PATH_EDGES:
        objective[W_INDEX[edge]] += 1

    return rows, rhs, equality, objective, labels
