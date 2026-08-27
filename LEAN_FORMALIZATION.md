# Lean 4 formalization and trust boundary

This repository contains a pinned Lean 4.33.1/mathlib 4.33.1 development of the proof reduction, exact LP certificate soundness, and an independent Lean-native replay of every checked certificate. The kernel now verifies a top-level theorem from a literal greedy run to the factor-two conclusion whose only finite-computation premise is the exact proposition `CertificateCoverage n`. This note separates that theorem from the evidence supplied by executing the checked-in certificate files.

## Reproduce the checks

From the repository root:

```bash
lake build GreedySuperstring
lake build checkCertificates
lake exe checkCertificates
```

The executable should print:

```text
Lean exact certificate replay passed
  five-input cases: 2880
  six-input representatives: 43200
  six-input cases covered by involution: 86400
```

The first command kernel-checks the complete imported theorem graph. The second compiles the independent executable. The third reads the compact certificate streams, rebuilds each integer LP, and checks every record exactly. The toolchain is fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Top-level kernel theorem

The principal declaration is:

```lean
GreedySuperstring.FormalTheorem.literalGreedyRun_factorTwo
    (data : WordInstance α n)
    (shortest : IsShortestCommonSuperstring data)
    (hn : 0 < n)
    (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g])
    (coverage : CorpusCoverage.CertificateCoverage n) :
    g.length ≤ 2 * data.optimumLength
```

`CertificateCoverage n` says exactly that every chronology in `Model.greedyEdgeOrders n` and every path in `Model.optimalPaths n` has a valid exact record for the deterministically rebuilt dense case. Inside the theorem, Lean proves all of the following rather than assuming them:

- reconstruction of original labels from the literal greedy run;
- canonical relabelling of its terminal Hamiltonian path;
- replay from the exact canonical initial component list;
- equality between feasible model edges and current component merges;
- greedy dominance and licensed rectangle inequalities;
- validity of every raw chronology edge;
- correctness of every generated dense coefficient, right-hand side, path equality, and objective coordinate;
- existence of an exact optimum Hamiltonian order from shortestness;
- scaled-dual weak duality and the final natural-number bound.

Two additional declarations connect pure checker acceptance to this theorem:

- `literalGreedyRun_factorTwo_of_positionalReplay` accepts a successful replay of a complete chronology/path product at arbitrary `n`;
- `five_input_literalGreedyRun_factorTwo_of_replay` accepts successful replay of the public five-input corpus format.

The latter uses `Checker.checkFiveCorpus_coverage_sound`, whose proof follows the exact row-major traversal and applies `checkRecord_sound` to every visited record.

## Kernel-checked module map

| Module | Kernel-checked content |
|---|---|
| `Word.lean` | Directed overlaps, exact merge length, endpoint inheritance, antichain preservation, directed triangles, conditional rectangles, and pair inequalities. |
| `Optimal.lean`, `OptimalBridge.lean` | Occurrence ordering, overlap-path telescoping, path lower bounds, and existence of an exact Hamiltonian order for a shortest common word. |
| `GreedyRun.lean`, `RunLabelling.lean` | Literal greedy execution, reducedness and coverage preservation, and reconstruction of labelled merge histories. |
| `PathState.lean`, `PathRun.lean` | Original-label components, exact endpoint interfaces, merge updates, length telescoping, and terminal Hamiltonian paths. |
| `Relabelling.lean` | Equivalence-based instance/run transport, permutation replay, and exact canonical-run construction. |
| `Relaxation.lean`, `PrimalBridge.lean` | Semantic finite word instances, all word-valid LP inequalities, and construction of the generated primal point. |
| `ChronologyBridge.lean`, `ChronologyConstruction.lean` | Automatic decoding of generated comparisons and derivation of chronology hypotheses from an actual labelled run. |
| `Model.lean`, `DenseEncodingCorrectness.lean` | Deterministic row generation, edge-index inversion, coefficient accumulation, and all five dense encoding laws. |
| `LP.lean`, `DenseLP.lean`, `Isomorphism.lean` | Denominator-cleared weak duality, record-to-scaled-dual reflection, factor-two soundness, and exact model transport. |
| `Certificate.lean`, `Checker.lean` | Compact parsing, Boolean record validity, per-record reflection, positional replay soundness, five-corpus coverage soundness, and kernel-computed enumeration/symmetry counts. |
| `EnumerationBridge.lean`, `CorpusCoverage.lean` | Completeness of the executable permutation generator and transport from semantic orders/runs to exact corpus coverage. |
| `EndToEnd.lean`, `LiteralEndToEnd.lean`, `FormalTheorem.lean` | Composition from literal greedy execution through exact certificates to `|G| ≤ 2 OPT`. |
| `SmallCardinality.lean` | Arithmetic core of the one-through-four input argument, including both four-input branches under the explicit `FourCase` disjunction. |

## Exact native replay

`Lean/Main.lean` invokes the independent checker on:

- 2,880 five-input records;
- 43,200 stored six-input representatives;
- all 86,400 six-input cases after checking the reverse-and-relabel involution and complete orbit coverage.

For each record the checker validates dimensions, nonzero scale, sparse index ranges and uniqueness, multiplier signs, every stationarity coordinate, the encoded dual bound, deterministic case order, corpus count, and source-corpus hash. For six inputs it additionally checks the 36-coordinate involution, row/right-hand-side multiset equality, objective invariance, transformed path equalities, and disjoint complete chronology-orbit coverage.

The compact Lean streams were deterministically converted from the public Python corpora. They are checked artifacts, not trusted inputs to the theorem prover:

| Stream | Records | SHA-256 |
|---|---:|---|
| `Lean/Data/five.cert` | 2,880 | `c66f8b7c269ec2f6f20a919ff3a1a3df1ef437571cfd655fa9e1a8efe23c5556` |
| `Lean/Data/six.cert` | 43,200 | `6e68dac563c588612a02a4ebdc99d4988450e3085ea96aff21f939d3ccd21c73` |

Their headers bind them to the original corpora:

| Source corpus | SHA-256 |
|---|---|
| `five_string_certificates.json` | `e733e5cb361e515db6fe257789f3991bf5f264a3f241814d9a74464439b0fe66` |
| `generalize/six_string_certificates.jsonl.gz` | `53ef042c6c7b4c59ca2beac9b960fcd99ea522956d3212efdbd122a35119ab01` |

`tools/convert_lean_certificates.py` is intentionally outside the trusted base. The Lean checker independently rejects malformed or invalid converted data.

## Axioms and computation

The theorem modules contain no `sorry`, `admit`, custom `axiom`, `unsafe` declaration, or `native_decide` proof. Lean reports only its standard dependencies:

```text
propext
Classical.choice
Quot.sound
```

The ordinary `decide` proofs of case counts and six-order orbit coverage depend only on `propext`. The executable uses compiled evaluation for speed.

## Exact remaining boundary

Successful `IO` execution is evidence from a verified checker implementation; it is not automatically a proposition stored in the Lean kernel. Consequently, this release does not claim a closed kernel declaration with no corpus premise that proves the entire one-through-six result from the checked-in files.

The earlier literal-run-to-LP gap is closed: `FormalTheorem.literalGreedyRun_factorTwo` leaves only `CertificateCoverage n`. Pure successful replay of a full positional corpus implies that proposition in the kernel, and this implication is specialized to the five-input checker. The checked-in files are loaded and replayed by native `IO`; their successful run is reported separately above. For six inputs, the native checker also validates the concrete representative-to-full-corpus LP symmetry, while the generic kernel module proves transport across an explicitly supplied model isomorphism.

The small-cardinality Lean module formalizes the Appendix A arithmetic but does not yet derive its `FourCase` disjunction from every literal run. Thus the public mathematical theorem and its exact Python verification cover one through six, while the strongest single Lean declaration is the corpus-conditional theorem displayed above. Turning the native file replay, concrete six-input symmetry transport, and the final small-cardinality case split into closed kernel data would remove the remaining boundary.

## Independent reruns

The Lean replay and the original standard-library Python replay use different parsers and checker implementations:

```bash
python3 verify_five_string_certificates.py five_string_certificates.json
python3 generalize/verify_six_string_certificates_v2.py \
  generalize/six_string_certificates.jsonl.gz
lake exe checkCertificates
```

Any mismatch is release-blocking.
