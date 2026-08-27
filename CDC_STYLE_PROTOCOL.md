# CDC-style protocol for the greedy superstring conjecture

## Exact task

Let `X` be a finite set of nonempty finite strings, with no member a substring of another. For strings `x,y`, let `ov(x,y)` be the greatest `k` such that the length-`k` suffix of `x` is the length-`k` prefix of `y`, and let `x merge y` be `x` followed by the suffix of `y` not included in that overlap.

A greedy run repeatedly chooses an ordered pair of distinct current strings maximizing `ov(x,y)` among all ordered pairs, replaces the pair by `x merge y`, and stops with one string `G`. Ties are arbitrary and adversarial. Let `OPT(X)` be the minimum length of a string containing every original member of `X` as a substring.

Resolve completely:

> For every such finite `X` and every greedy run, `|G| <= 2 OPT(X)`.

A complete negative resolution is an explicit `X` and legal greedy tie-breaking sequence with `|G| > 2 OPT(X)`, together with exact certificates of all overlaps, greedy maximality at every step, and an optimality certificate for `OPT(X)`.

## Reject list

The following do not resolve the task: fixed-size or fixed-alphabet verification; a proof only for five strings; a better upper bound still above 2; average or favorable tie-breaking; a reduction to an unproved statement of comparable strength; an abstract overlap matrix not proved realizable by strings; or a purported counterexample lacking greedy-legality and exact-OPT certificates.

Five strings are an important stepping stone, but must be labelled partial unless their proof supplies a mechanism extending to arbitrary cardinality.

## Search discipline

1. Maintain a diverse registry of mathematical families: directed-overlap inequalities, interval geometry in an optimal superstring, cycle-cover/Hamiltonian-path formulations, compression accounting, merge-history trees, minimal-counterexample induction, LP/dual certificates, word-equation realizability, and exact computation.
2. Preserve independence early. Do not tell most agents the favored route.
3. Require concrete lemmas, equations, constructions, executable checks, or counterexamples to sublemmas. Reject vague progress reports and any claim that a global compatibility step is routine.
4. Mark a family blocked when it reaches a missing lemma equivalent in strength to the target. Reopen only for a genuinely new invariant or construction.
5. Keep incompatible routes alive across rounds; cross-pollinate only after their actual gaps are visible.
6. Adversarially audit every candidate for: directed versus symmetric overlap; all maximum-overlap ties; new overlaps created after merging; accidental containment/duplicates; zero overlaps; repeated occurrences in an optimum; and the difference between a realizable string instance and a free weighted digraph.
7. Search public sources only for background and named results, not for a ready-made solution to this exact conjecture.
8. Repeatedly synthesize, challenge, redirect, and launch fresh rounds. A final mathematical claim must survive independent audit.

## Return condition

Return a complete proof or a fully certified counterexample if one survives audit. Otherwise preserve only rigorously proved intermediate results and state each exact gap; do not present partial progress as resolution.
