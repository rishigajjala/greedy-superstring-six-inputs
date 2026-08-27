# Soundness audit: from actual greedy runs to the six-string LP

The exact dual corpus proves an upper bound for a linear relaxation.  This
note checks, constraint by constraint, that every classical greedy run on six
reduced input strings maps into one of the certified LP cases.

## 1. Greedy merging as path-edge selection

For a substring-free input set, shortest-superstring optimization is a
permutation problem: an order `v_0,...,v_5` represents a superstring of length

`sum_i |v_i| - sum_i ov(v_i,v_(i+1))`.

The standard overlap-graph reformulation of greedy processes directed edges
in nonincreasing overlap order, accepting an edge precisely when its tail has
no accepted outgoing edge, its head has no accepted incoming edge, and it
does not close a directed cycle before the end.  Equivalently, accepted edges
are a directed path forest.  Nikolaev's 2024 survey makes this reduction
explicit: reduced SCS is a longest-Hamiltonian-path problem, the PATH
algorithm rejects exactly dominated or cycle-closing edges, and the locally
greedy string algorithm is a special case of PATH; classical greedy is a
special case of locally greedy.

For a chosen path forest `F`, an original edge `(i,j)` is extendible to a
Hamiltonian path if and only if:

* `i` has no outgoing edge in `F`;
* `j` has no incoming edge in `F`;
* `i` and `j` lie in different weak components of `F`.

This is exactly `feasible_edges` in the model.  A classical greedy choice has
weight at least every such edge.  Relabeling the final greedy path fixes it as
`0->1->...->5`; its five accepted edges can occur in any of `5!` orders.

As a hostile sanity check, 20,000 random six-word samples over a ternary
alphabet (lengths 2 through 7, rejecting non-reduced sets) were simulated by
literal string merging.  At every tested step, the current-string overlap
agreed with the original overlap between the two exposed path endpoints.  No
counterexample to the standard PATH representation was found.  This test is
only diagnostic; soundness relies on the established overlap-graph
reformulation, not on sampling.

## 2. An optimum supplies the equality row

Let `S*` be a shortest superstring.  Choose an occurrence of every reduced
input string and order the occurrences by starting position.  Their ending
positions have the same strict order: otherwise one chosen occurrence would
contain another, making one input a substring of another.  Empty gaps between
successive chosen intervals can be deleted, so a shortest superstring has an
order whose adjacent occurrence overlaps telescope to `|S*|`.

The maximum directed overlap of each adjacent pair is at least its overlap in
these occurrences.  Merging in this order therefore gives a superstring no
longer than `S*`; optimality forces equality.  Thus some permutation `P`
satisfies

`OPT = sum_i l_i - sum_(i,j in P) w_ij`.

After normalizing `OPT=1`, this is the equality row enumerated over all `6!`
paths.  It is unnecessary to add inequalities declaring `P` better than all
other paths: the actual point has that property, while omitting it only
enlarges each certified relaxation.

## 3. Every base row is necessary

After division by `OPT`:

* `0 <= l_i <= 1`, since every input occurs in an optimum;
* `0 <= w_ij <= l_i,l_j` by the definition of overlap;
* `w_ij+w_jk <= l_j+w_ik` is the directed distance triangle inequality;
* placing two nonnested occurrence intervals in `S*` gives
  `max(w_ij,w_ji) >= l_i+l_j-1`, hence the weaker sum row
  `w_ij+w_ji >= l_i+l_j-1`;
* at each greedy step, the selected edge dominates every feasible edge;
* when the two cross edges of a rectangle are feasible, both are dominated
  by the selected edge, so the conditional Monge inequality is licensed.

Finally, the selected path edges telescope exactly to the literal greedy
output length.  Therefore every actual normalized six-string run is feasible
in one enumerated LP case with objective equal to its approximation ratio.

## 4. Reverse-and-relabel symmetry

Let `r(i)=5-i` and transform variables by

`l'_i=l_r(i)`, `w'_ij=w_(r(j),r(i))`.

This corresponds to reversing all words and reflecting labels.  A selected
edge `(u,v)` becomes `(r(v),r(u))`.  Outdegree and indegree swap, weak
components are preserved, and therefore feasible-edge sets map bijectively.
Greedy rows map to greedy rows.  In a licensed Monge rectangle the two cross
edges swap roles and the bottom corner maps to the bottom corner, so its row
is invariant.  Caps, triangles, interval pairs, the canonical-path objective,
and the optimum equality (with the path reversed and reflected) also map
bijections.

Only the middle canonical edge is fixed by this involution.  No ordered list
of all five distinct canonical edges can therefore be fixed entrywise.  The
120 greedy orders split into exactly 60 two-element orbits, and enumerating
all 720 optimum paths for one order in each orbit covers all 86,400 cases.

## 5. Exact-dual verifier audit

For `min c*x` with `A*x<=b`, `e*x=1`, lower bounds, and upper bounds on the
six length variables, a stored certificate has multipliers

`y<=0`, free `z`, `q>=0`, `r<=0`

and verifies

`A^T y + e^T z + q + r = c`.

For every feasible `x`, this identity and the multiplier signs give

`c*x >= b^T y + z + sum_i r_i`.

The verifier reconstructs all coefficients and multipliers as exact
`Fraction` objects, rejects repeated/out-of-range sparse indices, checks that
no upper multiplier is attached to an unbounded overlap, checks all 36
stationarity coordinates, recomputes the dual bound, and requires it to be at
least `-2`.  It also verifies that the 60 representative orders and their
images are disjoint and cover all 120 orders, consumes exactly 43,200 records,
and rejects trailing records.

The independent run returned weakest dual bound `-2` and maximum support 29.
Consequently `-G>=-2`, hence `G<=2`, for every LP case and therefore for every
actual greedy run on six reduced strings.

## Conclusion

The six-string result is not merely a numerical observation and not merely a
statement about free weighted digraphs.  Subject to the standard and cited
GA-to-PATH overlap-graph equivalence, the exact certificates prove the actual
six-string greedy-superstring bound `|G| <= 2 OPT` for arbitrary alphabet,
arbitrary string lengths, and adversarial tie breaking.

Primary background: [Nikolaev, *Greedy Conjecture for the Shortest Common
Superstring Problem and its Strengthenings*](https://arxiv.org/html/2407.20422v1),
especially the permutation/overlap-graph reduction in Section 2 and the PATH
reformulation and Corollary 1 in Section 3.1.

