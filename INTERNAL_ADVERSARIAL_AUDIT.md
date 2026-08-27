# Internal adversarial audit of the five- and six-input certificates

Date: 2026-08-27

## Scope and verdict

This audit treated the proof reductions, LP builders, exact verifiers, and
certificate corpora as adversarial targets. It found no soundness error in the
factor-two result for five reduced strings or in the six-string relaxation
theorem and its implication for six reduced strings. The hostile checks did
not modify any model, generator, verifier, or certificate file; the sole
subsequent proof edit was the `m=1` repair recorded below.

The one proof omission found in the five-string review was the `m=1` case in
the preprocessing corollary: the old text said `m<=3` and then invoked a first
overlap, which does not exist for one surviving string. This has now been
patched in `FIVE_STRING_PROOF.md`: it treats `m=1` as immediate and begins the
overlap argument at `2<=m<=3`.

## Five strings

The audit read the full proof, model, verifier, and certificate corpus. It
checked the antichain/endpoint lemma (including zero overlaps, unequal
lengths, and crossing containment), the Hamiltonian-path formula for `OPT`,
both word inequalities, the `24 * 120` case reduction, feasible-edge logic,
every LP sign and normalization, the exact dual calculation, the four direct
separated-case arguments, and the lower-cardinality corollary.

The stock exact verification command returned:

```json
{
  "verified_cases": 2880,
  "weakest_dual_lower_bound": "-2",
  "maximum_certificate_support": 20
}
```

Independent checks:

- All 16 subsets of the canonical four-edge path agreed with an independent
  enumeration of Hamiltonian-path extensions. All 2,880 raw directed merge
  histories reduced to the 24 canonical chronologies, each with multiplicity
  120.
- Exhaustion over all ternary words of length at most four tested 216,769
  antichain triples and 387,336 globally maximizing ordered merges. This
  included 37,098 zero-overlap cases, 15,444 cases with both zero overlap and
  unequal selected lengths, and 156,780 unequal-length cases. Endpoint
  inheritance and antichain preservation had zero violations.
- Exhaustive superstring enumeration matched the maximum-overlap
  Hamiltonian-path formula on all 282 binary antichain sets of at most four
  words of length at most three, including 102 unequal-length sets.
- Direct word enumeration checked 27,000 directed triangles and 394,032
  applicable conditional rectangles (89,176 with a positive conclusion),
  with zero violations.
- The four-string exceptional claim was checked over all 288
  optimal-path/first-merge pairs. Exactly 24 first merges killed all three
  optimal edges, and every one was the reverse middle edge claimed.
- 450 exact random five-string GREEDY runs were mapped into their relabeled LP
  cases; 351 contained a selected zero-overlap step. No constraint failed.

Negative controls changed a used inequality multiplier's sign, changed its
value while preserving the sign, forged the encoded bound, deleted a case,
swapped cases, and changed a model coefficient with nonzero dual support.
Every corruption was rejected by the corresponding sign, stationarity,
bound, case-count, or case-order check.

## Six strings

The audit independently checked the integer model, its agreement with the
exploratory floating model, case coverage, the reversal-and-relabeling
involution, exact dual signs, the compressed corpus, and the bridge from real
GREEDY runs to the relaxation.

The full solver-independent verification returned:

```json
{
  "verified_representative_cases": 43200,
  "covered_cases_by_involution": 86400,
  "weakest_dual_lower_bound": "-2",
  "maximum_certificate_support": 29
}
```

An independent corpus scan found exactly 43,200 records, maximum support 29,
and maximum actual denominator 31. The generator's reported denominator
*limit* of 32 is therefore consistent.

Additional checks:

- For all 120 greedy chronologies, reversal/relabeling preserved the complete
  constraint-row multiset and objective. For all 720 optimal paths it
  preserved the equality. There were 60 representatives and no fixed greedy
  order.
- All 32 subsets of the canonical five-edge path agreed with independent
  Hamiltonian-extension enumeration. Exhausting all 86,400 directed merge
  histories produced all 120 canonical chronologies, each with multiplicity
  720.
- The exploratory and exact model builders agreed on every row, right-hand
  side, equality, and objective across all 120 chronologies and 720 paths.
- 160 exact random six-string GREEDY runs were mapped into the LP; 136 had a
  selected zero-overlap step, and none violated a constraint.
- Weak duality was rederived with the verifier's conventions: `y<=0` for
  `Ax<=b`, nonnegative lower-bound multipliers, nonpositive
  length-upper-bound multipliers, exact stationarity, and bound
  `b^T y + z + sum r_i`. The signs and normalization `OPT=1` are correct.

Negative controls changed a multiplier sign, perturbed a multiplier, forged
the bound, moved a certificate to the wrong path, changed a supported model
coefficient, truncated the gzip stream, and falsified the header certificate
count. Every change was rejected.

## Non-soundness-critical notes

- The original `verify_six_string_certificates.py` did not itself compare
  transformed row systems, equalities, and objectives. The independent audit
  filled that gap, and `verify_six_string_certificates_v2.py` now performs those
  exact symmetry checks mechanically.
- The original verifier validated only header format and certificate count.
  Version 2 now validates every metadata field as well as the exact record count.
- Six-string certificate records are positional rather than carrying explicit
  case identifiers. Each record is nevertheless tested against its expected
  case, so this is an auditability issue rather than a coverage defect.
- Each six-string chronology contains 25 identically zero degenerate Monge
  rows. They are harmless.
- The floating result JSON files contain ordinary solver-tolerance values such
  as ratios or overlaps a few ulps above 2 or 1. They are discovery artifacts,
  not proof witnesses; rational certificate verification is exact.
- The earlier `THEOREM_AND_WITNESSES.md` left the actual-string corollary
  implicit. `generalize/SIX_STRING_PROOF.md` now states and proves that bridge
  explicitly from the cardinality-independent lemmas in `FIVE_STRING_PROOF.md`.
