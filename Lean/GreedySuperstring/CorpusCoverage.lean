import GreedySuperstring.EndToEnd
import GreedySuperstring.EnumerationBridge

/-!
# Exact certificate-corpus coverage

This module states the precise theorem-level meaning of a complete executable
certificate corpus and connects it to the semantic per-Hamiltonian-order
premise used by the canonical labelled-run theorem.
-/

namespace GreedySuperstring

open GreedySuperstring.Relaxation
open ChronologyBridge
open EnumerationBridge

namespace CorpusCoverage

/-- Every case in the exact Cartesian product enumerated by `Model` has a
valid certificate for the dense case rebuilt from that chronology and path. -/
def CertificateCoverage (n : Nat) : Prop :=
  ∀ chronology ∈ Model.greedyEdgeOrders n,
    ∀ path ∈ Model.optimalPaths n,
      ∃ record : Certificate.Record,
        Checker.ValidFor
          (Model.buildCaseData n chronology path) record

/-- Exact corpus coverage supplies the semantic certificate premise for every
Hamiltonian order associated with a canonical labelled greedy run. -/
theorem everyOrderCertified_of_coverage
    {α : Type u} {n : Nat} [DecidableEq α]
    {data : WordInstance α n}
    {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    (canonical : CanonicalTerminalPath terminal)
    (coverage : CertificateCoverage n) :
    ∀ order : HamiltonianOrder n,
      ∃ record : Certificate.Record,
        Checker.ValidFor
          (PrimalBridge.generatedCaseData
            (modelChronology edges) order) record := by
  intro order
  have hchronology :
      modelChronology edges ∈ Model.greedyEdgeOrders n :=
    modelChronology_mem_greedyEdgeOrders run canonical
  have hpath :
      PrimalBridge.optimalPathLabels order ∈ Model.optimalPaths n :=
    optimalPathLabels_mem_optimalPaths order
  rcases coverage (modelChronology edges) hchronology
      (PrimalBridge.optimalPathLabels order) hpath with
    ⟨record, valid⟩
  exact ⟨record, by
    simpa [PrimalBridge.generatedCaseData] using valid⟩

/-- Integral factor-two bound for a canonical labelled run from exact corpus
coverage. Dense-layout correctness remains an explicit semantic premise. -/
theorem canonicalLabelledRun_factorTwo_int
    {α : Type u} {n : Nat} [DecidableEq α]
    (data : WordInstance α n)
    (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n))
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    (canonical : CanonicalTerminalPath terminal)
    (hn : 0 < n)
    (shortest : IsShortestCommonSuperstring data)
    (encoding :
      ∀ order : HamiltonianOrder n,
        PrimalBridge.DenseEncodingLaws data (modelChronology edges) order)
    (coverage : CertificateCoverage n) :
    (terminal.text.length : Int) ≤ 2 * data.optimumLength := by
  exact EndToEnd.canonicalLabelledRun_factorTwo_int data terminal edges run
    canonical hn shortest encoding
      (everyOrderCertified_of_coverage run canonical coverage)

/-- Natural-number form of `canonicalLabelledRun_factorTwo_int`. -/
theorem canonicalLabelledRun_factorTwo
    {α : Type u} {n : Nat} [DecidableEq α]
    (data : WordInstance α n)
    (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n))
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    (canonical : CanonicalTerminalPath terminal)
    (hn : 0 < n)
    (shortest : IsShortestCommonSuperstring data)
    (encoding :
      ∀ order : HamiltonianOrder n,
        PrimalBridge.DenseEncodingLaws data (modelChronology edges) order)
    (coverage : CertificateCoverage n) :
    terminal.text.length ≤ 2 * data.optimumLength := by
  exact EndToEnd.canonicalLabelledRun_factorTwo data terminal edges run
    canonical hn shortest encoding
      (everyOrderCertified_of_coverage run canonical coverage)

end CorpusCoverage

end GreedySuperstring
