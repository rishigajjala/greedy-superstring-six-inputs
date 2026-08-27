import GreedySuperstring.PrimalBridge
import GreedySuperstring.OptimalBridge

/-!
# One complete canonical LP case

This module composes the semantic primal construction with exact certificate
soundness.  It is the theorem-level boundary for a single canonical
chronology/optimal-path case.
-/

namespace GreedySuperstring.CaseTheorem

open GreedySuperstring.Relaxation

variable {α : Type u} {n : ℕ}

/-- Acceptance of the exact generated certificate proves factor two for the
semantic word instance represented by this canonical case. -/
theorem factorTwo_of_checkRecord
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n) (record : Certificate.Record)
    (hexact :
      (order.toOverlapPath data).superstring.length = data.optimumLength)
    (chronologySound :
      PrimalBridge.ChronologyHypotheses data chronology)
    (encoding : PrimalBridge.DenseEncodingLaws data chronology order)
    (accepted :
      Checker.checkRecord
        (PrimalBridge.generatedCaseData chronology order) record = .ok ()) :
    PrimalBridge.greedyLength data ≤ 2 * data.optimumLength := by
  exact DenseLP.factorTwo_of_checkRecord accepted
    (PrimalBridge.primalOf data chronology order hexact
      chronologySound encoding)
    (PrimalBridge.objective_identity data chronology order encoding)

/-- Equivalent form beginning with the pure theorem-level validity
predicate rather than the `Except` checker result. -/
theorem factorTwo_of_validRecord
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n) (record : Certificate.Record)
    (hexact :
      (order.toOverlapPath data).superstring.length = data.optimumLength)
    (chronologySound :
      PrimalBridge.ChronologyHypotheses data chronology)
    (encoding : PrimalBridge.DenseEncodingLaws data chronology order)
    (valid :
      Checker.ValidFor
        (PrimalBridge.generatedCaseData chronology order) record) :
    PrimalBridge.greedyLength data ≤ 2 * data.optimumLength := by
  exact DenseLP.factorTwo valid
    (PrimalBridge.primalOf data chronology order hexact
      chronologySound encoding)
    (PrimalBridge.objective_identity data chronology order encoding)

/-- If every nominated Hamiltonian order has an exact valid record, shortest
common-superstring minimality supplies the exact order needed for factor two.
This theorem isolates finite corpus coverage as the only certificate premise. -/
theorem factorTwo_of_every_order_certified
    (data : WordInstance α n) (hn : 0 < n)
    (shortest : IsShortestCommonSuperstring data)
    (chronology : List Model.Edge)
    (chronologySound :
      PrimalBridge.ChronologyHypotheses data chronology)
    (encoding :
      ∀ order : HamiltonianOrder n,
        PrimalBridge.DenseEncodingLaws data chronology order)
    (certified :
      ∀ order : HamiltonianOrder n,
        ∃ record : Certificate.Record,
          Checker.ValidFor
            (PrimalBridge.generatedCaseData chronology order) record) :
    PrimalBridge.greedyLength data ≤ 2 * data.optimumLength := by
  obtain ⟨order, exactOrder⟩ :=
    exists_exact_hamiltonian_order data hn shortest
  obtain ⟨record, valid⟩ := certified order
  exact factorTwo_of_validRecord data chronology order record exactOrder
    chronologySound (encoding order) valid

end GreedySuperstring.CaseTheorem
