# Every GREEDY run on six reduced strings has ratio at most two

## Theorem

Let `S={s_0,...,s_5}` be six nonempty finite strings over an arbitrary
alphabet, with no member a substring of another.  Every execution of the
standard greedy shortest-superstring algorithm, including adversarial tie
breaking, returns a superstring `G` satisfying

```text
|G| <= 2 OPT(S).
```

This is a fixed-cardinality, computer-assisted theorem.  It does not prove
the unrestricted Greedy Superstring Conjecture.

## 1. Why an actual GREEDY run is one of the finite LP cases

We import four self-contained lemmas from
[`FIVE_STRING_PROOF.md`](../FIVE_STRING_PROOF.md).  Their statements and
proofs do not use the number five and therefore apply verbatim to six (or any
finite number of) reduced strings.

1. **Greedy antichain and endpoint inheritance (Lemma 2.1 and Corollary
   2.2).**  If GREEDY merges current strings `A,B` at the current global
   maximum overlap, the merge preserves the substring antichain.  For every
   other current string `Z`,

   ```text
   ov(A merge B,Z)=ov(B,Z),    ov(Z,A merge B)=ov(Z,A).
   ```

   Hence every current component is a directed path through original labels,
   and the overlap between two components is the original overlap from the
   last label of the first path to the first label of the second.  If the five
   selected original arcs have total weight `S_G`, then

   ```text
   |G| = L-S_G,    L=sum_i |s_i|.
   ```

2. **Hamiltonian-path formula for OPT (Lemma 3.1).**  Ordering chosen
   occurrence intervals in a shortest superstring by their starts gives

   ```text
   OPT(S)=L-max_P sum_(i,j consecutive in P) ov(s_i,s_j),
   ```

   where `P` ranges over all permutations.  Thus at least one enumerated path
   gives the exact normalization equality used below.

3. **Directed triangle and conditional rectangle (Lemmas 4.1 and 4.2).**  For
   all strings `A,B,C`,

   ```text
   ov(A,B)+ov(B,C) <= |B|+ov(A,C).
   ```

   If a chosen edge `u->v` dominates the two feasible cross edges `u->v'`
   and `u'->v`, word alignment gives

   ```text
   w_(u,v')+w_(u',v) <= w_(u,v)+w_(u',v').
   ```

4. **Pair in an optimum (Lemma 4.3).**  If `O=OPT(S)`, every pair satisfies

   ```text
   w_ij+w_ji >= l_i+l_j-O.
   ```

Relabel the final greedy path as `0->1->...->5`.  Its five edges can have
been selected in any of `5!` chronological orders.  After any prefix, they
form a directed path forest.  An original edge is a possible current merge
exactly when its tail has no chosen outgoing edge, its head has no chosen
incoming edge, and its endpoints lie in different weak components.  This is
exactly the predicate `feasible_edges` in
[`six_string_lp_model.py`](six_string_lp_model.py).  Endpoint inheritance
shows that the selected edge dominates every edge declared feasible there;
ties are allowed.  It also licenses every conditional rectangle included by
the model.

Choose one optimal Hamiltonian path `P`.  Normalize `OPT=1`, put
`l_i=|s_i|/OPT` and `w_ij=ov(s_i,s_j)/OPT`, and combine the four lemmas above.
The actual run satisfies:

```text
0 <= l_i <= 1,
0 <= w_ij <= l_i,l_j,
w_ij+w_jk <= l_j+w_ik,
l_i+l_j-w_ij-w_ji <= 1,
all exact greedy-dominance rows,
all licensed conditional-rectangle rows,
sum_i l_i-sum_(i,j in P) w_ij = 1.
```

Its LP objective is exactly its normalized output length

```text
G = sum_i l_i-(w_01+w_12+w_23+w_34+w_45).
```

Therefore an upper bound for every enumerated LP case is automatically an
upper bound for every literal string run; no separate overlap-graph
equivalence theorem is assumed.

## 2. The exact finite theorem

There are `5!*6!=86,400` pairs of a greedy chronology and a nominated
optimal path.  For each pair the model minimizes `-G` subject to the rows
above.  The nominated path is not required to beat all other paths, so the
polyhedron is a relaxation of the actual-string case; proving an upper bound
on it is safe.

The corpus
[`six_string_certificates.jsonl.gz`](six_string_certificates.jsonl.gz)
contains exact sparse rational dual certificates for 43,200 representative
cases.  The remaining cases follow from the involution

```text
r(i)=5-i,
l'_i=l_(r(i)),
w'_ij=w_(r(j),r(i)),
order edge (u,v) -> (r(v),r(u)),
path (p_0,...,p_5) -> (r(p_5),...,r(p_0)).
```

It is an involution on all 36 variables, all greedy orders, and all optimal
paths.  It maps the full inequality/RHS multiset, the optimum equality, and
the objective exactly.  Only the middle canonical edge is fixed, so no
ordered list containing all five distinct canonical edges is fixed; the 120
chronologies form 60 two-element orbits.

Write a representative minimization LP as

```text
min c*x  subject to A*x<=b, e*x=1, x>=0, and l_i<=1,
```

where `c*x=-G`.  Each stored certificate gives exact multipliers

```text
y<=0, z free, q>=0, r<=0
```

such that

```text
A^T y+e^T z+q+r=c,
b^T y+z+sum_i r_i >= -2.
```

Weak duality gives `-G>=-2`, hence `G<=2`.

[`verify_six_string_certificates_v2.py`](verify_six_string_certificates_v2.py)
uses only the Python standard library and exact `Fraction` arithmetic.  It
validates every header field, sparse index, multiplier sign, stationarity
coordinate, and dual bound, and rejects missing or trailing records.  It
also independently checks:

* involutivity of the coordinate, edge, order, and path maps;
* disjointness and complete coverage of the 60 order representatives;
* exact row-with-RHS multiset and objective invariance for all 60 order pairs;
* exact equality invariance for all `60*720=43,200` path cases.

The generated model contains 25 identically zero conditional-rectangle rows
for every chronology.  These are degenerate licensed rectangles with a
repeated row or column, so they state `0<=0`.  They are retained because the
certificate corpus is indexed by row number.  Deleting them would only shift
indices: their RHS and coefficient vector are zero, so any multiplier on one
contributes neither to stationarity nor to the dual bound.

The verified weakest dual lower bound is `-2`, and the maximum certificate
support is 29.  Combining this finite theorem with Section 1 proves the
stated theorem for actual six-string GREEDY runs.

## 3. Reproduction and integrity

From the repository root, run:

```bash
shasum -a 256 \
  generalize/six_string_certificates.jsonl.gz

python3 generalize/verify_six_string_certificates_v2.py \
  generalize/six_string_certificates.jsonl.gz
```

The corpus is 897,380 bytes and has SHA-256

```text
53ef042c6c7b4c59ca2beac9b960fcd99ea522956d3212efdbd122a35119ab01
```

The verifier reports 43,200 representative cases, 86,400 covered cases, 60
exact inequality/RHS comparisons, 43,200 equality comparisons, weakest bound
`-2`, and maximum support 29.  Floating-point search files were used only for
discovery; neither the theorem nor its verification trusts them.
