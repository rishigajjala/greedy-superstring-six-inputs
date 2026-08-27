import GreedySuperstring.LiteralEndToEnd
import GreedySuperstring.CorpusCoverage
import GreedySuperstring.DenseEncodingCorrectness

/-!
# Final kernel-checked greedy-superstring theorem

The only computational premise below is exact coverage of the executable
certificate corpus.  Reverse labelling, canonical relabelling, chronology
validity, dense-layout correctness, and per-order certificate selection are
all derived inside Lean.
-/

namespace GreedySuperstring

open Relaxation
open ChronologyBridge

namespace FormalTheorem

variable {α : Type u} {n : Nat} [DecidableEq α]

/-- A singleton-ending literal greedy run is a factor-two approximation
whenever every executable case of the given cardinality has a valid exact
certificate. -/
theorem literalGreedyRun_factorTwo
    (data : WordInstance α n)
    (shortest : IsShortestCommonSuperstring data)
    (hn : 0 < n)
    (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g])
    (coverage : CorpusCoverage.CertificateCoverage n) :
    g.length ≤ 2 * data.optimumLength := by
  apply LiteralEndToEnd.literalGreedyRun_factorTwo
    data shortest hn g literal
  intro lift
  let result := lift.canonicalRelabelling
  change LiteralEndToEnd.RelabelledCaseCertificates result
  have canonical :
      CanonicalTerminalPath result.reindexedTerminal :=
    LiteralEndToEnd.canonicalTerminalPath_of_labels
      result.terminal_labels_canonical
  have validChronology :
      ∀ edge ∈ modelChronology result.chronology,
        PrimalBridge.EdgeValid n edge :=
    EnumerationBridge.modelChronology_edges_valid
      result.canonicalRun canonical
  refine {
    encoding := ?_
    certified := ?_
  }
  · intro order
    exact DenseEncodingCorrectness.denseEncodingLaws
      result.reindexedData (modelChronology result.chronology) order
      validChronology
  · exact CorpusCoverage.everyOrderCertified_of_coverage
      result.canonicalRun canonical coverage

/-- Successful replay of a full positional certificate array is sufficient
for the literal factor-two theorem.  This connects the generic checker
soundness theorem directly to the semantic result. -/
theorem literalGreedyRun_factorTwo_of_positionalReplay
    (data : WordInstance α n)
    (shortest : IsShortestCommonSuperstring data)
    (hn : 0 < n)
    (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g])
    (records : Array Certificate.Record) (checked : Nat)
    (accepted :
      Checker.checkPositionalCases n (Model.greedyEdgeOrders n)
        (Model.optimalPaths n) records = .ok checked) :
    g.length ≤ 2 * data.optimumLength := by
  apply literalGreedyRun_factorTwo data shortest hn g literal
  exact Checker.checkPositionalCases_sound accepted

/-- Five-input specialization tied to successful replay of the exact public
corpus format. -/
theorem five_input_literalGreedyRun_factorTwo_of_replay
    (data : WordInstance α 5)
    (shortest : IsShortestCommonSuperstring data)
    (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g])
    (header : Certificate.Header) (records : Array Certificate.Record)
    (accepted : Checker.checkFiveCorpus header records = .ok 2880) :
    g.length ≤ 2 * data.optimumLength := by
  apply literalGreedyRun_factorTwo data shortest (by omega) g literal
  exact Checker.checkFiveCorpus_coverage_sound accepted

end FormalTheorem

end GreedySuperstring
