import GreedySuperstring.CaseTheorem
import GreedySuperstring.ChronologyConstruction

/-!
# End-to-end factor-two theorem for a canonical labelled run

This module composes the literal labelled-run semantics, automatic chronology
alignment, exact dense certificates, and optimal Hamiltonian-order bridge.
It deliberately leaves dense-layout construction and automatic relabelling as
separate inputs.
-/

namespace GreedySuperstring

open GreedySuperstring.Relaxation
open ChronologyBridge
open ChronologyConstruction

namespace EndToEnd

variable {α : Type u} {n : Nat} [DecidableEq α]

/-- A canonical labelled greedy run whose chronology has a valid exact
certificate for every Hamiltonian order satisfies the factor-two bound.

Chronology soundness is not a hypothesis: it is constructed from `run` by
`chronologyAlignment_of_run`. -/
theorem canonicalLabelledRun_factorTwo_int
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
    (certified :
      ∀ order : HamiltonianOrder n,
        ∃ record : Certificate.Record,
          Checker.ValidFor
            (PrimalBridge.generatedCaseData
              (modelChronology edges) order) record) :
    (terminal.text.length : Int) ≤ 2 * data.optimumLength := by
  have alignment : ChronologyAlignment data terminal edges :=
    chronologyAlignment_of_run run
  have chronologySound :
      PrimalBridge.ChronologyHypotheses data (modelChronology edges) :=
    alignment.chronologyHypotheses
  have factorTwo :=
    CaseTheorem.factorTwo_of_every_order_certified data hn shortest
      (modelChronology edges) chronologySound encoding certified
  rw [alignment.greedyLength_eq_terminal_length canonical] at factorTwo
  exact factorTwo

/-- Natural-number form of `canonicalLabelledRun_factorTwo_int`. -/
theorem canonicalLabelledRun_factorTwo
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
    (certified :
      ∀ order : HamiltonianOrder n,
        ∃ record : Certificate.Record,
          Checker.ValidFor
            (PrimalBridge.generatedCaseData
              (modelChronology edges) order) record) :
    terminal.text.length ≤ 2 * data.optimumLength := by
  exact_mod_cast canonicalLabelledRun_factorTwo_int data terminal edges run
    canonical hn shortest encoding certified

end EndToEnd

end GreedySuperstring
