# The greedy shortest-superstring bound for at most six input words

This repository contains a formal manuscript and exact proof artifacts for the following fixed-input-cardinality result.

> **Theorem.** Let S be a reduced family of between one and six nonempty words over an arbitrary alphabet. Every legal run of the maximum-overlap greedy shortest-common-superstring algorithm returns a superstring G satisfying |G| <= 2 OPT(S).

The statement is uniform in the alphabet, word lengths, and all choices among tied maximum-overlap merges. The constant is sharp: an explicit five-word binary family has legal greedy ratios tending to 2.

**Status.** This is a new, deliberately unauthored computer-assisted research artifact dated 27 August 2026, pending human authorship review. It has undergone internal adversarial checks but has not been externally peer reviewed. It does **not** settle the unrestricted Greedy Superstring Conjecture, prove a seven-input theorem, or concern the separate problem where every input word has fixed length six.

## Read the paper

The polished manuscript is [The Greedy Shortest-Superstring Bound for at Most Six Input Words](output/pdf/greedy_shortest_superstring_at_most_six.pdf). Its source is [FORMAL_PAPER.md](FORMAL_PAPER.md).

## Verify the exact certificates

Certificate verification uses only Python 3.9+ and the standard library. From the repository root, run:

```bash
python3 verify_five_string_certificates.py five_string_certificates.json
python3 generalize/verify_six_string_certificates_v2.py \
  generalize/six_string_certificates.jsonl.gz
python3 verify_sharp_family.py --max-t 250
python3 verify_manifest.py
```

The exact summaries include:

| Inputs | Cases covered | Stored certificates | Weakest dual bound | Largest support |
|---:|---:|---:|---:|---:|
| 5 | 2,880 | 2,880 | -2 | 20 |
| 6 | 86,400 | 43,200 symmetry representatives | -2 | 29 |

The six-input verifier reconstructs the reverse-and-relabel involution and checks complete orbit coverage, row-multiset invariance, objective invariance, transformed path equalities, case order, metadata, and every exact rational dual certificate.

## Verify in Lean 4

The pinned Lean 4.33.1/mathlib 4.33.1 project kernel-checks the complete symbolic reduction from a literal greedy run to exact finite certificate coverage. Its top-level theorem, `FormalTheorem.literalGreedyRun_factorTwo`, proves `G <= 2*OPT` from the single proposition `CertificateCoverage n`; label reconstruction, canonical relabelling, chronology alignment, every generated dense coefficient, optimum-path normalization, and scaled Farkas weak duality are all discharged internally. Lean also contains an independent native exact checker for the finite corpora.

```bash
lake build
lake build checkCertificates
lake exe checkCertificates
```

Expected output:

```text
Lean exact certificate replay passed
  five-input cases: 2880
  six-input representatives: 43200
  six-input cases covered by involution: 86400
```

The checker rebuilds every integer LP row, validates denominator-cleared stationarity and bounds, and replays the complete six-input LP symmetry. `Checker.checkPositionalCases_sound` proves that successful pure replay of a full positional corpus supplies `CertificateCoverage n`; `Checker.checkFiveCorpus_coverage_sound` specializes this to the public five-input format. CI additionally runs an axiom audit that permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the formalization uses no `sorry`, `native_decide`, or custom axioms.

The precise remaining boundary is file execution: a successful native `IO` run is not itself stored as a kernel proposition, and the concrete six-input representative symmetry is verified by that native checker. The one-through-four arithmetic core is formalized separately, with its literal-run case split not yet assembled into the top-level theorem. See [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) for the theorem signatures and exact trust boundary.

## Build the PDF

The checked-in PDF was built with ReportLab 4.4.9:

```bash
python3 -m pip install -r requirements-paper.txt
python3 build_formal_paper.py
```

The output is written to `output/pdf/greedy_shortest_superstring_at_most_six.pdf`.

## Regenerate certificates (optional)

Regeneration is separate from verification and uses NumPy/SciPy for LP discovery before exact rational reconstruction:

```bash
python3 -m pip install -r requirements-generation.txt
python3 generate_five_string_certificates.py
python3 generalize/generate_six_string_certificates.py
```

The checked corpora are part of the proof; generation is not required to verify them.

## Repository map

- `FORMAL_PAPER.md`, `build_formal_paper.py`, and `output/pdf/`: manuscript source, builder, and rendered paper.
- `Lean/`, `lakefile.toml`, and `lean-toolchain`: theorem-bearing Lean modules, exact native checker, and pinned project configuration; [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) documents their scope.
- `five_string_lp_model.py`, `verify_five_string_certificates.py`, and `five_string_certificates.json`: five-input exact model, verifier, and corpus.
- `generalize/six_string_lp_model.py`, `generalize/verify_six_string_certificates_v2.py`, and the compressed corpus: six-input exact proof artifacts.
- `verify_sharp_family.py`: direct verification of the asymptotically sharp five-word family.
- `FIVE_STRING_PROOF.md` and `generalize/SIX_STRING_PROOF.md`: detailed proof notes.
- `INTERNAL_ADVERSARIAL_AUDIT.md` and `generalize/SIX_STRING_SOUNDNESS_AUDIT.md`: internal adversarial audit records.
- `CDC_STYLE_PROTOCOL.md`: the iterative conjecture/decompose/check prompting protocol used during discovery.
- `MANIFEST.sha256`: integrity hashes for the public release.

Exploratory seven-input searches and non-word-realizable LP obstructions are intentionally omitted from this theorem release.

## Proof architecture

The symbolic reduction proves that globally maximal greedy merges preserve the reduced substring antichain and inherit all external overlaps from path endpoints. Thus each run becomes an edge-selection chronology on original labels; an optimum is represented by a maximum-overlap Hamiltonian path; and literal overlap tables satisfy endpoint, triangle, rectangle, and pair inequalities.

For every canonical chronology/path pair, an explicit rational Farkas certificate proves the factor-two inequality over the necessary-condition polyhedron. Exact checkers reconstruct each integer row and verify multiplier signs, stationarity, and bounds without floating-point arithmetic.

## AI-use disclosure

The research workflow, exact-search code, manuscript, and internal audits were developed with substantial assistance from OpenAI Codex and multiple model instances. Explicit mathematical reductions and rational certificates make the result independently checkable; AI assistance is not a substitute for external peer review. Any submitting authors should review all artifacts and accept responsibility under the target venue's policy.

No license has yet been selected. The repository is public for inspection and verification; reuse rights remain reserved until a license is added.
