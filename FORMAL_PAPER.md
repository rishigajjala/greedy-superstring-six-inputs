---
title: The Greedy Shortest-Superstring Bound for at Most Six Input Words
subtitle: An Exact Computer-Assisted Proof
date: 27 August 2026
status: Unauthored technical manuscript - not peer reviewed
repository: https://github.com/rishigajjala/greedy-superstring-six-inputs
---

# Abstract

Let S be a finite substring antichain of nonempty words over an arbitrary alphabet. The greedy shortest-common-superstring algorithm repeatedly merges an ordered pair of current words having maximum directed suffix-prefix overlap, with ties resolved arbitrarily. We prove that if 1 <= |S| <= 6, then every greedy run returns a common superstring G satisfying |G| <= 2 OPT(S). The proof is exact and computer-assisted. A globally maximal merge is shown to preserve both the substring antichain and all endpoint overlap interfaces, reducing every literal run to an edge-selection chronology on the original labels. After relabeling the final greedy path, 2,880 five-input cases and 86,400 six-input cases remain. Exact rational Farkas certificates prove the factor-two bound in every case; a reverse-and-relabel involution reduces the stored six-input corpus to 43,200 representatives. Verification uses Python standard-library exact arithmetic, with an independent Lean 4 formalization of the complete literal-run-to-certificate-coverage reduction, exact certificate soundness, and a Lean-native exhaustive replay. A five-word binary family has legal greedy ratio 2 - 4/(t+4), so the constant is asymptotically sharp already for five inputs. This result does not settle the unrestricted Greedy Superstring Conjecture.

# 1. Introduction

The shortest common superstring problem asks for a shortest word containing every member of a finite input family as a contiguous substring. Tarhio and Ukkonen introduced and analyzed the natural greedy algorithm in 1988: repeatedly merge two current words having a maximum suffix-prefix overlap [2]. They conjectured that every run has approximation ratio at most two. Despite extensive work, the unrestricted conjecture remains open. The strongest published general upper bound for GREEDY is (sqrt(67)+2)/3, approximately 3.396 [3].

This paper concerns a different parameter: the number of input words. Alanko explicitly proposed the five-input case as a finite but nontrivial challenge [1]. We prove that challenge and one further case.

::: theorem Main theorem
Let Sigma be an arbitrary alphabet and let S be a finite set of nonempty words over Sigma, no one of which is a substring of another. If 1 <= |S| <= 6, then every run of the standard greedy shortest-superstring algorithm, including every resolution of overlap ties, returns a word G such that |G| <= 2 OPT(S).
:::

The parameterization must not be confused with recent work on inputs whose individual words have fixed length k. In particular, Chukhin, Kulikov, Mihajlin, and Smal prove lower bounds for words of length six [6]; their parameter is word length, whereas ours is input cardinality.

| Question | Parameter fixed | Status relevant here |
|---|---|---|
| Unrestricted Greedy Conjecture | Neither | Open; not settled here |
| Fixed word length k | Length of each input word | Separate line of work [6] |
| Present theorem | Number of reduced input words | Ratio at most 2 for 1 through 6 |

The proof has three conceptual components. First, a structural lemma shows that a globally maximal greedy merge preserves the substring antichain and inherits all external overlaps from its two endpoints. Thus every current word can be represented exactly by a directed path through original inputs. Second, an optimal superstring is equivalent to a maximum-overlap Hamiltonian path through the reduced input family. Third, after canonical relabeling, finitely many chronology/path pairs remain. A necessary-condition linear program is associated with each pair, and exact rational dual certificates prove the desired bound.

The finite calculation is part of the proof. Floating-point optimizer output is used only during discovery and contributes nothing to the theorem. The certificate checkers reconstruct every integer row, check every multiplier sign and stationarity coordinate with fractions.Fraction, and verify the exact bound. Sections 8 and 9 give the reproducibility ledger and the exact scope of the Lean 4 development.

# 2. Definitions and conventions

A word is a finite sequence over an arbitrary alphabet Sigma. For words x and y, define the directed overlap

```text
ov(x,y) = max { k : suffix_k(x) = prefix_k(y) }.
```

The quantity is directed: ov(x,y) need not equal ov(y,x). For distinct words x and y, their maximum-overlap merge is

```text
x merge y = x followed by y[ov(x,y):].
```

An input set is reduced if it is a substring antichain: no member is a substring of another. Standard preprocessing deletes duplicate words and every word contained in another; this does not change OPT. The theorem concerns GREEDY after this preprocessing. It does not identify such a run with an arbitrary run on an unreduced collection.

Starting with a reduced set S, GREEDY repeatedly chooses an ordered pair of distinct current words x,y for which ov(x,y) is globally maximum among all ordered pairs, replaces x,y by x merge y, and stops when one word remains. Every tie may be resolved adversarially.

For an original input s_i, write

```text
l_i = |s_i|,      w_ij = ov(s_i,s_j),      L = sum_i l_i.
```

Let OPT(S) denote the minimum length of a common superstring. All words are nonempty, so OPT(S)>0.

::: corollary Preprocessing formulation
For an arbitrary finite collection I, first delete duplicates and words contained in other members. If the surviving antichain S has between one and six members, then every subsequent greedy run satisfies |G| <= 2 OPT(I), because OPT(S)=OPT(I).
:::

# 3. Structural reduction to original-label paths

The next lemma is the essential bridge between literal string merging and the finite overlap model. Global maximality is indispensable.

::: lemma Endpoint inheritance and antichain preservation
Suppose the current words form a substring antichain. GREEDY chooses A,B with k=ov(A,B) equal to the current global maximum, and let M=A merge B. For every other current word Z,

```text
ov(M,Z) = ov(B,Z),          ov(Z,M) = ov(Z,A).
```

Moreover, replacing A,B by M leaves a substring antichain.
:::

**Proof.** The word M has A as a prefix and B as a suffix, so ov(M,Z) >= ov(B,Z). Put r=ov(M,Z). If r <= |B|, the length-r suffix of M is the length-r suffix of B, and hence r <= ov(B,Z). If r>|B|, then the part of this alignment ending at the end of A has length r-|B|+k>k. It is simultaneously a suffix of A and a prefix of Z, contradicting global maximality. Thus ov(M,Z)=ov(B,Z).

The reverse identity is symmetric. Since A is a prefix of M, ov(Z,M) >= ov(Z,A). If r=ov(Z,M)>|A|, then the portion extending into B gives an overlap from Z to B of length r-|A|+k>k, again contradicting maximality. Otherwise the matched prefix lies inside A, giving equality.

It remains to exclude containment. Because the current family is an antichain, k<|B|, so M is strictly longer than its prefix A. No old word can contain M because it would contain A. Conversely, suppose M contains an old word Z. An occurrence wholly inside the displayed copy of A or B contradicts the old antichain. Any crossing occurrence begins before the displayed copy of B and ends after the end of A. Its prefix through the end of A is then a suffix of A and a prefix of Z of length greater than k, contradicting maximality. Thus no containment is created. QED.

::: corollary Path-state invariant
Attach to each current word the ordered list of original labels merged into it. At every step these lists form vertex-disjoint directed paths. If P and Q are two current components, then

```text
ov(text(P),text(Q)) = w_(last(P),first(Q)).
```

Consequently every greedy step joins the end of one original-label path to the beginning of another. If the selected original arcs have total weight S_G, then the final greedy length is

```text
G = L - S_G.
```
:::

**Proof.** Induct on the number of merges. The endpoint identities in the lemma preserve every external interface exactly, and the total length drops by precisely the selected overlap at each step. QED.

# 4. Optimal superstrings and universal overlap inequalities

::: lemma Hamiltonian-path formula for OPT
For every reduced family S={s_0,...,s_(n-1)},

```text
OPT(S) = min_P (L-W(P)) = L-max_P W(P),
W(P)   = sum_(r=0)^(n-2) w_(p_r,p_(r+1)),
```

where P ranges over all permutations (p_0,...,p_(n-1)).
:::

**Proof.** Choose one occurrence interval of every input in a shortest common superstring. Two chosen intervals cannot be nested, because that would make one input a substring of another. Ordering intervals by their starting positions therefore orders their ending positions strictly as well.

For consecutive intervals of words i,j, let d be the displacement between their starts. If they overlap geometrically, the common block is a suffix of i and a prefix of j, so w_ij >= l_i-d. If they do not overlap, the same inequality is trivial. Thus d >= l_i-w_ij. Summing the displacements and the final word length shows that the superstring has length at least L-W(P) for the induced order P.

Conversely, for any order P, place each next word after the preceding word using their directed overlap. Reducedness makes every such overlap proper, so the right endpoint advances by l_j-w_ij>0. The resulting word contains every input and has length exactly L-W(P). Taking minima proves the formula. QED.

We use three further word inequalities. Their arrow orientations matter.

::: lemma Directed overlap triangle
For all words A,B,C,

```text
ov(A,B)+ov(B,C) <= |B|+ov(A,C).
```
:::

**Proof.** If ov(A,B)+ov(B,C)-|B| is positive, the two matched portions of B intersect in a block that is simultaneously a suffix of A and a prefix of C. Otherwise the assertion is immediate. QED.

::: lemma Conditional directed rectangle
Let a=ov(A,B), x=ov(A,C), and z=ov(D,B). If a>=x and a>=z, then

```text
ov(D,C) >= max(0,x+z-a).
```
:::

**Proof.** The length-a alignment A->B identifies prefix_x(C) with the interval [a-x,a] in prefix_a(B). The alignment D->B identifies suffix_z(D) with [0,z]. Their intersection has length max(0,x+z-a) and is simultaneously a suffix of D and a prefix of C. QED.

At a greedy step selecting u->v, every feasible cross edge u->v' and u'->v has weight at most w_uv. Therefore the preceding lemma licenses

```text
w_(u,v') + w_(u',v) <= w_(u,v) + w_(u',v').
```

::: lemma Pair in an optimum
If all inputs occur in a word of length O, then for every pair i,j,

```text
w_ij+w_ji >= l_i+l_j-O.
```
:::

**Proof.** Order chosen occurrences by their starts. If i begins before j at displacement d, then d+l_j<=O. When the occurrences intersect, w_ij>=l_i-d>=l_i+l_j-O; when they do not, the right side is nonpositive. Adding w_ji>=0 proves the assertion. The other start order is symmetric. QED.

# 5. Canonical cases and the necessary-condition LP

Fix n in {5,6}. By the path-state invariant, the final greedy word determines a Hamiltonian path through the original labels. Relabel that final path as

```text
0 -> 1 -> ... -> n-1.
```

Its canonical edges are e_i=(i,i+1), 0<=i<n-1, but GREEDY may have selected them in any chronological order sigma, a permutation of the n-1 edges. After a prefix of sigma, the chosen edges form a path forest whose components are exactly the joined contiguous blocks of the canonical final path.

A directed edge (u,v) is feasible at that stage precisely when u has no selected outgoing edge, v has no selected incoming edge, and u,v lie in different weak components of the selected forest. This is exactly the set of current literal merges by endpoint inheritance.

Let P be a nominated optimal Hamiltonian path. Normalize OPT=1 and introduce n^2 variables

```text
l_i = |s_i|/OPT,          w_ij = ov(s_i,s_j)/OPT   (i!=j).
```

For each pair (sigma,P), define Q_(sigma,P)^(n) by the following constraints.

1. Nonnegativity and endpoint caps:

```text
0 <= l_i <= 1,       0 <= w_ij <= l_i,       0 <= w_ij <= l_j.
```

2. Every directed triangle, for distinct i,j,k:

```text
w_ij+w_jk <= l_j+w_ik.
```

3. Every pair-in-an-optimum row:

```text
l_i+l_j-w_ij-w_ji <= 1.
```

4. At each chronology step, if e is selected and f is any feasible edge,

```text
w_e >= w_f.
```

5. At each chronology step selecting u->v, every conditional rectangle for feasible cross edges u->v' and u'->v:

```text
w_(u,v')+w_(u',v) <= w_(u,v)+w_(u',v').
```

6. The nominated optimal-path equality:

```text
sum_i l_i - sum_(ij consecutive in P) w_ij = 1.
```

The objective is the normalized greedy output length

```text
G = sum_i l_i - sum_(i=0)^(n-2) w_(i,i+1).
```

::: proposition Soundness of the relaxation
Every literal greedy run on n reduced inputs, together with any optimal Hamiltonian path supplied by the OPT formula, gives a point of exactly one Q_(sigma,P)^(n), and its LP objective is |G|/OPT.
:::

**Proof.** Relabel the final original-label path canonically and record its actual selection chronology. Endpoint inheritance identifies current merges with the feasible-edge predicate, so global greedy maximality gives every dominance row and licenses every included rectangle. The word lemmas give endpoint, triangle, and pair rows. The optimal Hamiltonian path gives the equality, and telescoping gives the objective. QED.

The polyhedron is deliberately a relaxation. It neither asserts that every feasible overlap matrix is realizable by words nor requires P to dominate every other Hamiltonian path. Omitting such conditions enlarges the feasible set, so an upper bound on Q_(sigma,P)^(n) remains valid for literal strings.

# 6. Exact dual certificates

Write the minimization form of a case as

```text
minimize c^T x = -G
subject to A x <= b,     e^T x = 1,
           x >= 0,       l_i <= 1.
```

The upper bounds l_i<=1 are kept separate below.

::: lemma Exact certificate criterion
Suppose there are rational multipliers y<=0, a free rational z, lower-bound multipliers q>=0, and length-upper-bound multipliers r<=0 such that

```text
A^T y + e z + q + r = c
```

coordinatewise, and

```text
b^T y + z + sum_i r_i >= -2.
```

Then every feasible point satisfies G<=2.
:::

**Proof.** For any feasible x,

```text
c^T x = y^T A x + z e^T x + q^T x + r^T l
        >= y^T b + z + sum_i r_i
        >= -2.
```

The first inequality uses y<=0 with Ax<=b, q>=0 with x>=0, and r<=0 with l_i<=1. Since c^T x=-G, the conclusion follows. QED.

All stored multipliers are exact rationals. The verifiers reject an incorrect sign, duplicate or out-of-range sparse index, stationarity mismatch, forged bound, missing case, extra record, or unexpected metadata.

## 6.1. Five inputs

There are 4! possible greedy chronologies and 5! nominated paths, hence

```text
4! * 5! = 2,880
```

cases. The exact corpus contains one certificate for every case.

::: theorem Five-input finite certificate theorem
Every point in every Q_(sigma,P)^(5) satisfies G<=2.
:::

The standard-library verifier confirms all 2,880 certificates. The weakest dual lower bound is exactly -2 and the largest certificate support is 20.

## 6.2. Six inputs and the symmetry involution

There are

```text
5! * 6! = 86,400
```

raw chronology/path pairs. Define r(i)=5-i and transform variables by

```text
l'_i  = l_(r(i)),
w'_ij = w_(r(j),r(i)).
```

This reverses every directed edge and reflects the canonical labels. It maps a canonical edge (i,i+1) to (4-i,5-i), and maps a path (p_0,...,p_5) to

```text
(r(p_5),...,r(p_0)).
```

Endpoint caps, directed triangles, pair rows, exact feasible-edge sets, licensed rectangles, the optimum equality, and the objective are invariant. The map is an involution. Only the middle canonical edge is fixed, so no ordered list containing all five distinct canonical edges can be fixed entrywise. Thus the 120 chronologies split into 60 two-element orbits.

::: theorem Six-input finite certificate theorem
Every point in every Q_(sigma,P)^(6) satisfies G<=2.
:::

The corpus stores certificates for 60*720=43,200 representatives. The strengthened verifier checks the variable permutation, edge/order/path involutivity, disjoint orbit representatives, complete coverage of all 120 chronologies, exact row-with-right-hand-side multiset invariance for all 60 order pairs, objective invariance, all 43,200 transformed path equalities, every metadata field, and every exact dual certificate. The weakest bound is -2 and the largest certificate support is 29.

::: theorem Main theorem, completed
For every reduced input family S with 1<=|S|<=6, every greedy run satisfies |G|<=2 OPT(S).
:::

**Proof.** The cases |S|<=4 are proved without computation in Appendix A. For five or six inputs, map the actual run and an optimal path into the corresponding normalized relaxation by the soundness proposition. The exact finite certificate theorem for that cardinality gives G<=2, and rescaling yields |G|<=2 OPT(S). QED.

# 7. Sharpness at five inputs

::: proposition Asymptotic sharpness
For every integer t>=3, the five binary words

```text
A = 001,          B = 0 1^(t-1),
C = 101,          D = 1^(t-1) 0,
E = 1^t
```

form a reduced family with a legal greedy run of length 2t+4 and optimum t+4. Hence the ratio is

```text
(2t+4)/(t+4) = 2 - 4/(t+4),
```

which tends to two.
:::

**Proof.** The five words are distinct and no shorter word occurs in a longer one, so the family is reduced. Consider the run

```text
B -> D          overlap t-1,
C -> (B merge D) overlap 2,
A -> ...         overlap 1,
E -> ...         overlap 0.
```

At the first step no proper overlap can exceed t-1, and B->D attains it. After this merge, C and A each have overlap two into the composite and no larger overlap exists. After choosing C, every positive remaining overlap has length one. After choosing A, both directions involving E have overlap zero. Thus every displayed step is globally greedy, including all ties.

The total input length is 3t+6 and the run saves (t-1)+2+1=t+2, so its output has length 2t+4. The order A,B,E,D,C saves

```text
2 + (t-1) + (t-1) + 2 = 2t+2
```

and therefore gives a superstring of length t+4. This is optimal. If a Hamiltonian path uses two of the three weight-(t-1) arcs B->E, B->D, E->D, its other two edges have weight at most two, giving total saving at most 2(t-1)+4. If it uses at most one long arc, its saving is at most (t-1)+6<=2t+2 for t>=3; with no long arc it is at most 8<=2t+2. Thus no path saves more than 2t+2. QED.

::: corollary Exact fixed-cardinality constant
The supremum of the worst greedy ratio over reduced instances with at most six inputs is exactly two. The lower bound already occurs as a limit over instances with exactly five inputs.
:::

# 8. Reproducibility and integrity ledger

The certificate corpora are part of the proof. The repository contains the integer model builders, deterministic generators, exact verifiers, corpora, manuscript source, and audit notes. No commercial solver or third-party Python package is used during verification.

| Inputs | Raw cases covered | Stored certificates | Corpus bytes | SHA-256 |
|---:|---:|---:|---:|---|
| 5 | 2,880 | 2,880 | 2,221,399 | e733e5cb361e515db6fe257789f3991bf5f264a3f241814d9a74464439b0fe66 |
| 6 | 86,400 | 43,200 | 897,380 | 53ef042c6c7b4c59ca2beac9b960fcd99ea522956d3212efdbd122a35119ab01 |

From the repository root, run

```text
python3 verify_five_string_certificates.py five_string_certificates.json

python3 generalize/verify_six_string_certificates_v2.py \
  generalize/six_string_certificates.jsonl.gz

python3 verify_sharp_family.py --max-t 250
```

The expected exact summaries are

```text
five: verified_cases=2880,
      weakest_dual_lower_bound=-2,
      maximum_certificate_support=20

six: verified_representative_cases=43200,
     covered_cases_by_involution=86400,
     weakest_dual_lower_bound=-2,
     maximum_certificate_support=29

sharpness: t=3..250 verified
```

The six-input records are positional rather than carrying explicit case identifiers. This is an auditability limitation, not a coverage gap: the verifier deterministically regenerates the expected chronology/path order and tests each record against its corresponding case. It rejects missing or trailing records.

An internal adversarial audit independently rederived the bridge lemmas, feasible-edge predicate, weak-duality signs, symmetry, and case counts. It also performed exhaustive small-word tests, cross-implementation comparisons, random literal-run embeddings, and negative controls that deliberately corrupted signs, values, bounds, row coefficients, case order, stream length, and metadata. These checks are internal validation, not independent peer review.

# 9. Lean 4 formalization and exact replay

The repository includes a project pinned to Lean 4.33.1 and mathlib 4.33.1. The kernel-checked development formalizes directed overlap and merge lemmas, preservation of the reduced antichain, endpoint inheritance, occurrence ordering and Hamiltonian-path length bounds, literal and labelled greedy runs, exact path-length telescoping, automatic canonical relabelling and chronology alignment, every deterministic dense row and objective coordinate, the static relaxation inequalities, denominator-cleared Farkas weak duality, and transport across exact LP model isomorphisms.

These pieces are composed in `FormalTheorem.literalGreedyRun_factorTwo`. Given a nonempty finite word instance, shortestness of its nominated common word, a literal singleton-ending greedy run, and the exact proposition `CertificateCoverage n`, the theorem concludes that the literal output length is at most twice optimum. `CertificateCoverage n` states only that every executable chronology/path pair has a valid exact record. Thus label reconstruction, relabelling, feasibility, generated primal construction, dense-array correctness, optimum-path existence, and weak duality are no longer external premises.

A separate Lean-native executable rebuilds the deterministic integer LPs and replays the complete compact certificate streams. From the repository root, run

```text
lake build GreedySuperstring
lake build checkCertificates
lake exe checkCertificates
```

The final command reports

```text
Lean exact certificate replay passed
  five-input cases: 2880
  six-input representatives: 43200
  six-input cases covered by involution: 86400
```

For every record, the Lean checker validates dimensions, scale, sparse-index uniqueness and range, multiplier signs, denominator-cleared stationarity, and the exact dual bound. For six inputs it independently checks the 36-coordinate reverse-and-relabel map, row/right-hand-side multiset invariance, objective and path-equality transport, disjoint chronology orbits, and complete coverage of all 86,400 cases.

The theorem modules contain no `sorry`, `admit`, custom axiom, `unsafe` declaration, or `native_decide` proof. The continuous-integration axiom audit reports only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`.

The distinction between the two Lean layers is material. Successful execution of an `IO` checker is not itself a proposition stored in the Lean kernel. The kernel proves that successful pure positional replay supplies certificate coverage, and it specializes this implication to the five-input corpus checker. The checked-in files are nevertheless parsed and executed by native `IO`, so the present release does not claim that their successful run is already stored as a closed kernel proposition. For six inputs, the native checker additionally validates the concrete representative-to-full-corpus LP symmetry; the kernel separately proves generic transport across an explicitly supplied model isomorphism.

Accordingly, the earlier literal-run-to-generated-primal integration gap is closed. The remaining boundary for one closed file-backed declaration is proof-producing or kernel-reflected corpus ingestion, the concrete six-input symmetry transport, and the final derivation of the four-input `FourCase` split from every literal run. This separation does not weaken the mathematical computer-assisted proof in Sections 3 through 6, whose public exact corpora are independently replayed by the standard-library Python verifier. The exact module map, theorem signatures, axiom report, and artifact hashes are recorded in `LEAN_FORMALIZATION.md`.

# 10. Scope and limitations

This manuscript proves a fixed-input-cardinality theorem only. It does not prove or disprove the unrestricted Greedy Superstring Conjecture, and it establishes neither a seven-input theorem nor a seven-input counterexample.

The necessary-condition LP used here is sufficient through six inputs but admits non-word-realizable points above ratio two at seven inputs. This is evidence that pairwise overlaps, triangles, rectangles, and pair-in-an-optimum inequalities do not by themselves characterize global word realizability. Separate occurrence-alignment and periodicity lemmas in the research notes eliminate the saved abstract obstructions, but they do not classify every seven-input case and are not used in the theorem proved here.

The result is a new computer-assisted research artifact and has not been externally peer reviewed. Before journal submission, human authors should check every mathematical argument, fix authorship and licensing, archive the exact corpora and source at an immutable repository, and take responsibility for the claims.

# 11. AI-use disclosure

This draft, its exact-search code, certificate-generation workflow, and internal adversarial audits were developed with substantial assistance from OpenAI Codex and multiple model instances. The final theorem is supported by explicit mathematical reductions and independently checkable rational certificates, but AI assistance is not a substitute for external peer review. Any submitting authors must review the manuscript and proof artifacts in full and accept responsibility under the target venue's policy.

# References

[1] J. N. Alanko. Attacking the greedy superstring conjecture with AI. Blog post, 20 January 2026. [Online version](https://blog.jnalanko.net/2026/01/20/attacking-the-greedy-superstring-conjecture-with-ai/) (accessed 27 August 2026).

[2] J. Tarhio and E. Ukkonen. A greedy approximation algorithm for constructing shortest common superstrings. Theoretical Computer Science 57(1):131-145, 1988. [doi:10.1016/0304-3975(88)90167-3](https://doi.org/10.1016/0304-3975%2888%2990167-3).

[3] M. Englert, N. Matsakis, and P. Vesely. Approximation Guarantees for Shortest Superstrings: Simpler and Better. In 34th International Symposium on Algorithms and Computation (ISAAC 2023), LIPIcs 283, Article 29, 2023. [doi:10.4230/LIPIcs.ISAAC.2023.29](https://doi.org/10.4230/LIPIcs.ISAAC.2023.29).

[4] M. Nikolaev. Greedy Conjecture for the Shortest Common Superstring Problem and its Strengthenings. arXiv:2407.20422v1, 2024. [arXiv:2407.20422](https://arxiv.org/abs/2407.20422).

[5] M. Nikolaev. All instantiations of the greedy algorithm for the shortest superstring problem are equivalent. arXiv:2102.05579v1, 2021. [arXiv:2102.05579](https://arxiv.org/abs/2102.05579).

[6] N. Chukhin, A. S. Kulikov, I. Mihajlin, and A. Smal. The Greedy Superstring Algorithm Achieves Ratio 2 for Strings of Length 6 Already. arXiv:2608.20018v2, 2026. [arXiv:2608.20018](https://arxiv.org/abs/2608.20018).

[7] A. Schrijver. Theory of Linear and Integer Programming. Wiley, 1986.

# Appendix A. The cases of at most four reduced inputs

The case m=1 is immediate. Suppose 2<=m<=3, and let a be the first maximum overlap selected by GREEDY. Every edge of an optimal Hamiltonian path has weight at most a, so

```text
L = OPT+W(P*) <= OPT+(m-1)a.
```

GREEDY saves at least a. Therefore

```text
G <= OPT+(m-2)a <= 2 OPT,
```

because a is at most the length of an input word and hence at most OPT.

Now let m=4, and denote the three optimal-path overlaps by p,q,r in order. Endpoint caps give

```text
L >= p+r+max(p,q)+max(q,r),
```

and consequently

```text
2(p+q+r)-L <= min(p,q)+min(q,r).                 (A.1)
```

Let a,b be the first two greedy overlaps. If at least one optimal edge remains feasible after the first merge, then

```text
b >= min(p,q,r),
a >= max(min(p,q),min(q,r)).
```

Since min(p,q,r)=min(min(p,q),min(q,r)), their sum is at least the right side of (A.1), proving the desired bound.

The only directed merge that can make all three edges of a four-vertex optimal path infeasible is the reverse middle edge. Relabel the optimum as A->B->C->D and suppose GREEDY selects C->B with weight a. Directed triangles leave feasible edges

```text
w_AC >= p+q-|B|,         w_BD >= q+r-|C|.
```

Thus

```text
b >= max(0,p+q-|B|,q+r-|C|).
```

Put x=p+q-|B| and y=q+r-|C|. Endpoint caps imply x<=p<=a and y<=r<=a, so

```text
x+y <= a+max(0,x,y) <= a+b.
```

Finally,

```text
2(p+q+r)-L-a-b
 <= p+2q+r-|B|-|C|-a-b
  = x+y-a-b
 <= 0.
```

Hence G<=2 OPT for four inputs as well.

# Appendix B. Exact row schema and deterministic case order

For fixed n, the canonical greedy edges are stored as

```text
E = ((0,1),(1,2),...,(n-2,n-1)).
```

Chronologies are lexicographically ordered permutations of E. Optimal paths are lexicographically ordered permutations of range(n). For a selected chronology prefix, feasibility is determined by the following mathematical predicate.

```text
feasible(u,v,chosen):
    reject if u=v
    reject if u already has a chosen outgoing edge
    reject if v already has a chosen incoming edge
    reject if u and v are in the same weak component of chosen
    otherwise accept
```

Rows are emitted in a fixed family order: endpoint caps, directed triangles, pair rows, then stepwise greedy-dominance and licensed rectangle rows. The optimum equality and objective are generated separately. Integer coefficients are used throughout; normalization enters only through right-hand sides equal to zero or one.

For n=6 the stored order first selects the 60 lexicographically chosen representatives of the reverse-and-relabel chronology orbits, then all 720 nominated paths. The v2 verifier recomputes the orbit and equality maps rather than trusting the header.

# Appendix C. Certificate representation and checker logic

Each sparse certificate stores the claimed bound, nonzero inequality multipliers y, nonzero lower multipliers q, nonzero length-upper multipliers r, and the free equality multiplier z. Rational numbers are encoded as strings accepted by fractions.Fraction. The checker rejects duplicate sparse indices and verifies the expected sign before any arithmetic.

For each case it rebuilds A,b,e,c and performs the following exact checks.

```text
1. Decode every multiplier as a rational number.
2. Check y<=0, q>=0, r<=0 and all sparse index ranges.
3. Accumulate A^T y + e z + q + r coordinatewise.
4. Require exact equality with c in every coordinate.
5. Compute beta = b^T y + z + sum_i r_i exactly.
6. Require beta to equal the stored bound and beta>=-2.
7. Reject a missing certificate or any trailing record.
```

For six inputs, the checker additionally constructs the 36-coordinate involutive variable permutation, compares complete row/right-hand-side multisets, compares objectives, verifies all transformed equalities, and checks exact orbit coverage.

# Appendix D. Internal audit summary

The internal hostile audit included the following independent checks.

- All path-forest subsets agreed with an independently written Hamiltonian-extension enumerator.
- Every raw merge history reduced to the expected canonical chronology multiplicity.
- Small-word exhaustions found no violation of endpoint inheritance, antichain preservation, directed triangles, or conditional rectangles.
- Literal optimal-superstring enumeration agreed with the Hamiltonian-path formula on exhaustive small antichains.
- Random five- and six-word literal greedy runs mapped into their nominated LP cases without a failed row, including many zero-overlap selections.
- The exploratory floating and exact integer model builders agreed row for row.
- Deliberately corrupted certificates were rejected for bad signs, changed values, forged bounds, changed row coefficients, missing records, swapped case order, truncated streams, and false metadata.

The five-input review found one expository omission: the preprocessing corollary originally invoked a first overlap when only one word survived. The statement was repaired by separating m=1 before the m=2,3 argument. No theorem-level defect was found in the final package.
