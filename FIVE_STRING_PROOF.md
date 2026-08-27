# The factor-two bound for every GREEDY run on five reduced strings

## Status and theorem

This is a complete, computer-assisted proof for the fixed-cardinality case
of five strings.  The finite part is certified by exact rational dual
certificates; no floating-point LP output is trusted.

**Theorem.**  Let
```
S = {s_0,s_1,s_2,s_3,s_4}
```
be five nonempty finite strings, with no member a substring of another.
Every run of standard GREEDY, including every adversarial resolution of
ties, returns a common superstring of length at most
`2 OPT(S)`.

This is a fixed-size result, not a resolution of the unrestricted Greedy
Conjecture.

## 1. Exact formulation

For strings `x,y`, let
```
ov(x,y) = max { k : suffix_k(x) = prefix_k(y) }.
```
This is a **directed** quantity: in general
`ov(x,y) != ov(y,x)`.  Put
```
x ⊙ y = x followed by y[ov(x,y):].
```

Standard GREEDY maintains a collection of current strings.  While at least
two remain, it chooses two distinct current strings `x,y` for which the
directed overlap `ov(x,y)` is maximum over all ordered pairs of distinct
current strings, and replaces them by `x ⊙ y`.  There is no favorable
tie rule: any maximizer may be chosen.  The algorithm does not silently
replace a directed overlap by `max(ov(x,y),ov(y,x))`.

The input is already reduced.  We do not assume that arbitrary merges
preserve reduction; that fact is proved below for the merges actually made
by GREEDY.

Write
```
l_i = |s_i|,              w_ij = ov(s_i,s_j),              L = Σ_i l_i.
```

## 2. A greedy merge preserves the antichain and its endpoint interfaces

The next lemma is the point at which newly created strings and possible
containment have to be treated exactly.

**Lemma 2.1 (antichain and endpoint inheritance).**  Suppose the current
strings form a substring antichain.  GREEDY chooses the ordered pair
`A,B`, and
```
k = ov(A,B)
```
is the current global maximum.  Let `M=A⊙B`.  For every other current
string `Z`,
```
ov(M,Z) = ov(B,Z),                         (2.1)
ov(Z,M) = ov(Z,A).                         (2.2)
```
Moreover, replacing `A,B` by `M` leaves a substring antichain.

**Proof.**  The word `M` has `A` as a prefix and `B` as a suffix.
Consequently `ov(M,Z) >= ov(B,Z)`.  Put `r=ov(M,Z)`.  If
`r <= |B|`, the length-`r` suffix of `M` is the length-`r`
suffix of `B`, and hence `r <= ov(B,Z)`.  If instead `r>|B|`,
the overlap begins in the `A` part of `M`.  Its portion ending at
the end of `A` has length
```
r-|B|+k > k
```
and is simultaneously a suffix of `A` and a prefix of `Z`.  Thus
`ov(A,Z)>k`, contradicting greedy maximality.  This proves (2.1).
For (2.2), `ov(Z,M)>=ov(Z,A)` because `A` is a prefix of `M`.
Put `r=ov(Z,M)`.  If `r<=|A|`, the matched prefix of `M` is a
prefix of `A`, giving the reverse inequality.  If `r>|A|`, the final
`r-|A|+k>k` letters of that matched prefix of `M` form a prefix of
`B`; they are also a suffix of `Z`.  This would give
`ov(Z,B)>k`, contradicting maximality.

It remains to exclude new containment.  Since the current state is an
antichain, `k<|B|`, so `M` is strictly longer than its prefix `A`.
If an old string `Z` contained `M`, it would contain `A`, a
contradiction.

Conversely, suppose `M` contains `Z`.  An occurrence wholly inside
the displayed copy of `A` or of `B` contradicts the old antichain.
Any other occurrence starts at a position `p<|A|-k` and ends after
position `|A|`.  The prefix of that occurrence ending at `|A|`
is then a suffix of `A` of length
```
|A|-p > k,
```
so `ov(A,Z)>k`, again a contradiction.  Therefore no containment is
created. ∎

The global-maximum hypothesis is essential.  Endpoint inheritance can fail
for an arbitrary pair of composite strings merged out of greedy order.
We use the lemma only at an actual GREEDY step.

Attach to every current string the ordered list of original strings merged
into it.  Induction using Lemma 2.1 gives:

**Corollary 2.2 (path-state invariant).**  At every time, the component
lists are disjoint directed paths through the original labels.  If current
components `P,Q` have first and last original labels
`first(P),last(P)` and `first(Q),last(Q)`, then
```
ov(text(P),text(Q)) = w_{last(P),first(Q)}.                 (2.3)
```
Thus a GREEDY step joins the end of one current path to the beginning of
another.  In particular, no containment cleanup is triggered later.

If the four selected original arcs have total weight `S_G`, telescoping
the total length of the current collection gives
```
G = L-S_G.                                                  (2.4)
```

## 3. OPT is a maximum-overlap Hamiltonian path

**Lemma 3.1.**  For a reduced family of strings,
```
OPT = min_P (L-W(P)) = L-max_P W(P),                        (3.1)
```
where `P=(p_0,...,p_{n-1})` ranges over permutations and
```
W(P)=Σ_{r=0}^{n-2} w_{p_r,p_{r+1}}.
```

**Proof.**  In a shortest common superstring choose an occurrence interval
of each input string.  Two chosen intervals cannot be nested, since that
would make one input a substring of another.  Therefore ordering them by
their starts also orders their ends strictly.

For consecutive intervals of strings `i,j`, let `d` be the difference
of their start positions.  If they overlap geometrically, their common
part proves `w_ij >= l_i-d`; if they do not, the same inequality is
trivial.  Hence `d >= l_i-w_ij`.  Summing the start increments and the
last length proves that this superstring has length at least `L-W(P)`
for the induced order `P`.

Conversely, for every order `P`, place each next string after the previous
one using the displayed directed overlap `w_{p_r,p_{r+1}}`.  This gives
a common superstring of length exactly `L-W(P)` (one need not insist
that a larger accidental composite overlap be used).  The two bounds give
(3.1). ∎

Fix an optimal order `P^*`.  By (2.4) and (3.1), the theorem is exactly
```
2W(P^*)-S_G <= L.                                           (3.2)
```

## 4. Two word inequalities

**Lemma 4.1 (directed overlap triangle).**  For any strings `A,B,C`,
```
ov(A,C) >= ov(A,B)+ov(B,C)-|B|.                             (4.1)
```

When the right side is positive, intersect the copy of the prefix of `B`
coming from `A→B` with the copy of the suffix of `B` going into
`B→C`.  The intersection is a suffix of `A` and a prefix of `C`.
When it is nonpositive there is nothing to prove.

**Lemma 4.2 (conditional directed rectangle).**  Put
```
a=ov(A,B),   x=ov(A,C),   z=ov(D,B).
```
If `a>=x` and `a>=z`, then
```
ov(D,C) >= max(0,x+z-a).                                   (4.2)
```

**Proof.**  The equality `suffix_a(A)=prefix_a(B)` identifies
`prefix_x(C)` with the interval `[a-x,a]` of that prefix of `B`.
Likewise `suffix_z(D)` is the interval `[0,z]`.  Their intersection
has length `max(0,x+z-a)`; it is a suffix of `D` and a prefix of
`C`. ∎

Notice all four arrows in (4.2).  The conclusion is `D→C`, not
`C→D`, and no symmetric-pair overlap has been substituted.

At a GREEDY step selecting `u→v`, every feasible cross edge
`u→v'` and `u'→v` has weight at most `w_uv`.  Lemma 4.2 therefore
licenses the linear inequality
```
w_{u'v'} >= w_{uv'}+w_{u'v}-w_{uv}.                        (4.3)
```

We also use one interval inequality.

**Lemma 4.3 (pair in an optimum).**  If all inputs occur in a word of
length `O`, then for every pair `i,j`,
```
w_ij+w_ji >= l_i+l_j-O.                                    (4.4)
```

Indeed, order chosen occurrences of `i,j` by their starts.  If `i`
starts first at displacement `d`, then `d+l_j<=O` after restricting
to the span of the whole superstring, and the geometric overlap gives
`w_ij>=l_i-d>=l_i+l_j-O` whenever the last quantity is positive.
The reverse start order gives the other directed overlap.

## 5. Relabeling a complete run

By Corollary 2.2, the final GREEDY component is an ordered path through the
five labels.  Relabel its order as
```
0 → 1 → 2 → 3 → 4.
```
The selected edges are then
```
e_0=(0,1), e_1=(1,2), e_2=(2,3), e_3=(3,4),
```
but they may have been selected in any of the `4!` chronological orders.
After any prefix of that chronological order, the current components are
exactly the contiguous blocks of `0,1,2,3,4` joined by the edges already
selected.  Every feasible directed merge is the last label of one block
to the first label of a different block.

An optimal Hamiltonian path may be any of the `5!` permutations.
Consequently every run/optimum pair belongs to exactly one of
```
4! · 5! = 2880                                             (5.1)
```
finite order pairs.  Equal overlap weights cause no omitted case: a
particular adversarial tie resolution simply chooses one of the 24
chronologies.

## 6. The exact finite certificate theorem

This section is the computer-assisted portion of the proof.

For each of the 2880 pairs, introduce the 25 nonnegative variables
`l_i,w_ij`.  Normalize `OPT=1`.  The model contains:

1. the endpoint caps `w_ij<=l_i,l_j`;
2. all directed triangles (4.1);
3. all interval-pair inequalities (4.4);
4. at every chronological step, `w_selected>=w_candidate` for every
   feasible directed path-forest extension;
5. every conditional rectangle (4.3) for which both cross edges are
   feasible at that step;
6. the equality
   `Σl_i-Σ_{ij in P^*}w_ij=1`;
7. `0<=l_i<=1`, the upper bound following from `l_i<=OPT`.

The nominated path is not constrained to dominate all other paths.  Thus
this is a relaxation of the string problem, which makes its upper bound
safe.

**Finite certificate theorem.**  In every one of these 2880 rational
polyhedra,
```
Σ_i l_i - (w_01+w_12+w_23+w_34) <= 2.                      (6.1)
```

The integer model is
[five_string_lp_model.py](five_string_lp_model.py).  The certificate file
is [five_string_certificates.json](five_string_certificates.json), and
[verify_five_string_certificates.py](verify_five_string_certificates.py)
checks it using only `fractions.Fraction` and the Python standard library.
For every case it checks multiplier signs, exact coefficient stationarity,
and the exact dual bound.  It does not invoke an LP solver.

Run
```bash
python3 verify_five_string_certificates.py \
  five_string_certificates.json
```
from the repository root.  The verified result is
```json
{
  "verified_cases": 2880,
  "weakest_dual_lower_bound": "-2",
  "maximum_certificate_support": 20
}
```

This exact certificate theorem is the rigorous closure of the finite
nonexceptional classification; it should not be described as a
human-only enumeration.

For auditing, the cases divide as follows.  Among the 24 chronological
orders, 12 have first two selected final-path edges meeting and 12 have
them disjoint.  This gives `1440` meeting cases.  In a disjoint case,
write the first two arcs as `X→Y` and `U→V`, with fifth vertex `E`.
Exactly four of the 120 comparison paths put both tails first, then `E`,
then both heads:
```
X,U,E,Y,V;   X,U,E,V,Y;   U,X,E,Y,V;   U,X,E,V,Y.          (6.2)
```
There are therefore `12·4=48` separated cases and
`1440+(1440-48)=2832` nonseparated cases.  The exact verifier supplies
a Farkas certificate for every one of the 2832 nonseparated cases (and,
in fact, for the 48 cases too).  The next section gives a direct word-level
closure of the 48 delicate cases, independently auditing the part for
which free overlap-matrix relaxations are weakest.

## 7. Direct closure of the 48 separated cases

Let the first two disjoint greedy arcs be
```
X→Y of weight a,                 U→V of weight c,
```
in that chronological order.  Hence `c<=a`.  Let `h` be the third
greedy overlap; the fourth overlap is nonnegative and may be discarded.
In each of the four orders below, write
`alpha,beta,gamma,delta` for the four consecutive comparison-path
overlaps in order.

### 7.1 Order X,U,E,Y,V

Here
```
(alpha,beta,gamma,delta) = (w_XU,w_UE,w_EY,w_YV).
```
Greedy dominance gives
```
alpha,gamma <= a,                 beta,delta <= c.
```
The first rectangle gives the currently feasible edge
```
w_EU >= alpha+gamma-a,
```
and the second gives the feasible edge
```
w_YE >= beta+delta-c.
```
Thus, with
```
r=alpha+gamma-a,  s=beta+delta-c,  H=max(0,r,s),
```
we have `h>=H`.  Put `m=max(beta,gamma)`.  Endpoint caps give
```
L >= 2a+c+max(c,alpha)+m.                                  (7.1)
```
Also `W(P)=a+c+r+s`.  It is enough to prove
```
2r+2s-H <= a+max(c,alpha)+m.                               (7.2)
```
If `H=0`, this is immediate.  If `H=r`, then
```
2r+2s-H = r+2s <= alpha+2 beta
                    <= a+max(c,alpha)+m.
```
If `H=s`, then
```
2r+2s-H = 2r+s <= 2 alpha+beta
                    <= a+max(c,alpha)+m.
```
Here we used `r<=alpha`, `s<=beta`, `alpha<=a`,
`beta<=a`, and `m>=beta`.  Equations (7.1)-(7.2) give
`2W(P)<=L+a+c+h`.

### 7.2 Order U,X,E,V,Y

Here
```
(alpha,beta,gamma,delta) = (w_UX,w_XE,w_EV,w_VY).
```
Greedy dominance gives
```
alpha,gamma <= c,                 beta,delta <= a.
```
The two available rectangle conclusions are
```
w_VE >= beta+delta-a,             w_EX >= alpha+gamma-c.
```
Set
```
r=beta+delta-a,  s=alpha+gamma-c,  H=max(0,r,s),
m=max(beta,gamma).
```
Then `h>=H`,
```
L>=2a+2c+m,                       W(P)=a+c+r+s.
```
It remains to show `2r+2s-H<=a+c+m`.  If `H=r`,
```
r+2s <= beta+2alpha <= a+c+m
```
because `2alpha<=a+c`.  If `H=s`,
```
2r+s <= 2beta+alpha <= a+c+m
```
because `alpha+beta<=a+c` and `m>=beta`.  The case
`H=0` is immediate.

### 7.3 Nested order X,U,E,V,Y (the first arc is outer)

Here
```
(alpha,beta,gamma,delta) = (w_XU,w_UE,w_EV,w_VY).
```
Greedy dominance gives
```
alpha,delta <= a,                 beta,gamma <= c.
```
The first rectangle gives a **reverse inner** overlap
```
q = w_VU >= max(0,alpha+delta-a).                           (7.3)
```
This `q` is not the selected overlap `c=w_UV`.
Put `u=|U|`, `v=|V|`, and `m=max(beta,gamma)`.
The directed triangle lemma gives the currently feasible edges
```
w_VE >= q+beta-u,                 w_EU >= gamma+q-v.
```
Therefore
```
h >= max(0,q+beta-u,q+gamma-v).                            (7.4)
```
We claim
```
u+v+h >= 2q+m.                                             (7.5)
```
If `m=beta` and `u>=q+m`, then (7.5) follows from
`v>=q`.  Otherwise (7.4) gives `u+h>=q+m`, again with
`v>=q`.  The case `m=gamma` is symmetric.

Now (7.3) gives `alpha+delta<=a+q`, while
`beta+gamma<=c+m`.  Also
```
L>=2a+u+v+m.
```
Using `c<=a` and (7.5),
```
2W(P)
 <= 2a+2q+2c+2m
 <= 3a+c+2q+2m
 <= L+a+c+h.
```

### 7.4 Nested order U,X,E,Y,V (the first arc is inner)

Here
```
(alpha,beta,gamma,delta) = (w_UX,w_XE,w_EY,w_YV).
```
Greedy dominance gives
```
alpha,delta <= c,                 beta,gamma <= a.
```
The second rectangle gives the reverse inner overlap
```
q = w_YX >= max(0,alpha+delta-c),                           (7.6)
```
again distinct from the selected `a=w_XY`.  Put
```
x=|X|,  y=|Y|,  m=max(beta,gamma).
```
Triangles give feasible edges and hence
```
h >= max(0,q+beta-x,q+gamma-y).                            (7.7)
```
Let `H=max(0,q+m-a)`.  Then
```
x+y+h >= 2a+H.                                             (7.8)
```
For `m=beta`, if `q+m<=a`, the bounds `x,y>=a` suffice.
If `q+m>a` and `x>=q+m`, then
`x+y>=q+m+a=2a+H`.  Otherwise (7.7) gives
`x+h>=q+m` and `y>=a`.  The `m=gamma` case is symmetric.

Set `A=alpha+delta` and `B=beta+gamma`.  We have
```
A<=2c,       B<=2m,       q>=max(0,A-c),
L>=2c+x+y+m.
```
Equations (7.6)-(7.8) imply
```
L+a+c+h >= 3a+3c+m+max(0,A-c+m-a).                         (7.9)
```
It remains to compare `2A+2B` with the right side.  Since
`B<=2m`, and
```
F(A)=2A-max(0,A-c+m-a)
```
is increasing for `0<=A<=2c`, it suffices to take `A=2c`.
The remaining assertion is
```
c+3m-3a <= max(0,c+m-a).                                  (7.10)
```
If `c+m<=a`, the left side is
`(c+m-a)+2(m-a)<=0`.  If `c+m>a`, subtracting the
right side leaves `2(m-a)<=0`.  Thus (7.10), (7.9), and
`2W(P)=2A+2B` finish the fourth order.

All inequalities in this section are non-strict.  In particular, the
argument includes `a=c` and every tie at the third and fourth steps.

## 8. Completion of the theorem

Choose the chronology and optimal order induced by the given instance and
the given adversarial GREEDY run.  Lemmas 2.1-3.1 show that the real string
data satisfy every constraint in its finite certificate case.  The exact
dual certificate yields (6.1), which rescales to
```
G <= 2 OPT.
```
The antichain proof shows that no unmodeled containment deletion or
full-overlap merge appears, and endpoint inheritance shows that every
modeled edge has the correct directed overlap even after composite strings
have been formed.

## 9. Inputs whose initial substring preprocessing leaves fewer strings

The main theorem is scoped to an already reduced set of exactly five
strings.  If a standard implementation first deletes duplicates and
strings contained in others and leaves `m<=5` strings, the same factor-two
statement follows as follows.

The case `m=1` is immediate.  For `2<=m<=3`, let `a` be the first maximum overlap.  An optimal path has
`m-1` edges, each at most `a`, so
```
L = OPT+W(P^*) <= OPT+(m-1)a.
```
GREEDY saves at least `a`, whence
```
G <= OPT+(m-2)a <= 2OPT
```
because `a<=OPT`.

For `m=4`, let the optimal-path overlaps be `p,q,r`.  Endpoint caps give
```
L >= p+r+max(p,q)+max(q,r),
```
and hence
```
2(p+q+r)-L <= min(p,q)+min(q,r).                            (9.1)
```
Let the first two greedy weights be `a,b`.  If at least one optimal edge
remains feasible after the first merge, then
```
b >= min(p,q,r)
```
and `a>=max(min(p,q),min(q,r))`; thus `a+b` is at least
the right side of (9.1).

The only way one directed merge can make all three edges of a four-vertex
path infeasible is that the optimum is
```
A→B→C→D
```
and GREEDY selects the reverse middle edge `C→B`.  Put
`a=w_CB`.  Triangles leave the feasible edges
```
w_AC >= p+q-|B|,             w_BD >= q+r-|C|,
```
so
```
b >= max(0,p+q-|B|,q+r-|C|).
```
Writing `x=p+q-|B|` and `y=q+r-|C|`, endpoint caps give
`x<=p<=a` and `y<=r<=a`.  Therefore
```
x+y <= a+max(0,x,y) <= a+b.
```
But
```
2(p+q+r)-L-a-b
 <= p+2q+r-|B|-|C|-a-b
 = x+y-a-b <= 0.
```
Thus `m=4` also satisfies the factor-two bound.  The case `m=5` is
the theorem above.  This corollary concerns GREEDY run *after* standard
substring preprocessing; it does not identify that run with an arbitrary
run on an unreduced multiset.

## 10. The constant two is asymptotically sharp already for five strings

For every integer `t>=3`, take the binary strings
```
A = 001,                  B = 0 1^(t-1),
C = 101,                  D = 1^(t-1) 0,
E = 1^t.
```
They form a substring antichain. The following adversarial greedy run is
legal:
```
B -> D       overlap t-1,
C -> (B⊙D)   overlap 2,
A -> ...     overlap 1,
E -> ...     overlap 0.
```
At the first step no proper overlap can exceed `t-1`, and `B->D`
attains it. After that merge, both `C->(B⊙D)` and
`A->(B⊙D)` have overlap two and no remaining overlap is larger.
After the second merge, all positive remaining overlaps have length one;
after the third, both directions involving `E` have overlap zero. Thus
every displayed choice is a global maximum, including all ties.

The total input length is `3t+6`, and the displayed run saves
```
(t-1)+2+1+0 = t+2,
```
so its output length is
```
G_t = 2t+4.
```

The order
```
A, B, E, D, C
```
saves `2+(t-1)+(t-1)+2=2t+2` and spells
```
00 1^t 01,
```
of length `t+4`. It is optimal: among `B,E,D`, the only overlaps of
order `t` are the three forward edges `B->E`, `B->D`, and `E->D`, all
of weight `t-1`; a Hamiltonian path can use at most two of them, and
each of its other two edges has weight at most two. Hence no path saves
more than `2(t-1)+4=2t+2`. (For `t=3`, the same bound follows simply
because every proper overlap is at most two.)

Consequently
```
G_t / OPT_t = (2t+4)/(t+4) = 2-4/(t+4) -> 2.
```
The proved factor is therefore best possible even at exactly five inputs.
