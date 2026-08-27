import GreedySuperstring.Relabelling
import GreedySuperstring.EndToEnd

/-!
# End-to-end factor two from a literal greedy run

This module reconstructs original labels from a literal singleton-ending
greedy run, relabels its terminal path into canonical order, and applies the
exact certified LP theorem to that reindexed instance and chronology.
-/

namespace GreedySuperstring

open Relaxation
open ChronologyBridge

namespace LiteralEndToEnd

variable {α : Type u} {n : Nat} [DecidableEq α]

/-- A labelled lift of a singleton-ending literal greedy run. -/
structure LiteralLift (data : WordInstance α n) (g : Word α) where
  terminal : PathComponent (Fin n) α
  edges : List (Fin n × Fin n)
  run : LabelledGreedyRun data.overlap
    (initialComponents data.word (List.ofFn id)) [terminal] edges
  terminal_text : terminal.text = g

namespace LiteralLift

/-- Reverse labelling constructs a lift of every literal greedy run. -/
theorem nonempty_of_literal
    (data : WordInstance α n) (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g]) :
    Nonempty (LiteralLift data g) := by
  have hreduced :
      Reduced ((List.ofFn (id : Fin n → Fin n)).map data.word) := by
    simpa [List.map_ofFn, Function.comp_def] using data.reduced
  have literal' :
      GreedyRun
        ((List.ofFn (id : Fin n → Fin n)).map data.word) [g] := by
    simpa [List.map_ofFn, Function.comp_def] using literal
  obtain ⟨terminal, edges, run, htext⟩ :=
    exists_labelled_terminal_of_literal hreduced data.maximum literal'
  exact ⟨{
    terminal := terminal
    edges := edges
    run := run
    terminal_text := htext
  }⟩

/-- Canonically relabel a chosen literal lift by its terminal label order. -/
noncomputable def canonicalRelabelling
    {data : WordInstance α n} {g : Word α}
    (lift : LiteralLift data g) :
    CanonicalRunRelabelling data lift.terminal lift.edges :=
  lift.run.canonicalRelabelling data lift.terminal lift.edges

end LiteralLift

/-- Exact dense-layout and certificate coverage for the reindexed data and
chronology selected by one canonical relabelling. -/
structure RelabelledCaseCertificates
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (result : CanonicalRunRelabelling data terminal edges) : Prop where
  encoding :
    ∀ order : HamiltonianOrder n,
      PrimalBridge.DenseEncodingLaws result.reindexedData
        (modelChronology result.chronology) order
  certified :
    ∀ order : HamiltonianOrder n,
      ∃ record : Certificate.Record,
        Checker.ValidFor
          (PrimalBridge.generatedCaseData
            (modelChronology result.chronology) order)
          record

namespace CanonicalRunRelabelling

/-- Shortestness transports exactly to the reindexed instance. -/
theorem reindexed_shortest_iff
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
  (result : CanonicalRunRelabelling data terminal edges) :
    IsShortestCommonSuperstring result.reindexedData ↔
      IsShortestCommonSuperstring data := by
  unfold GreedySuperstring.CanonicalRunRelabelling.reindexedData
  exact data.reindex_shortest_iff result.order.labelEquiv

/-- The reindexed instance has the same optimum coordinate. -/
@[simp] theorem reindexed_optimumLength
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
  (result : CanonicalRunRelabelling data terminal edges) :
    result.reindexedData.optimumLength = data.optimumLength := by
  simp [GreedySuperstring.CanonicalRunRelabelling.reindexedData]

end CanonicalRunRelabelling

/-- Mapping adjacent finite labels to executable edges agrees with the
model's generic consecutive-edge construction. -/
private theorem map_modelEdge_adjacentEdges
    (labels : List (Fin n)) :
    (adjacentEdges labels).map modelEdge =
      Model.pathEdges (labels.map Fin.val) := by
  cases labels with
  | nil => rfl
  | cons first rest =>
      induction rest generalizing first with
      | nil => rfl
      | cons second remaining ih =>
          simp only [adjacentEdges, List.map_cons, Model.pathEdges,
            List.tail_cons, List.map_cons, List.zip_cons_cons]
          congr 1
          simpa [Model.pathEdges] using ih second

/-- Erasing the bounds from the canonical finite enumeration gives the
ordinary natural-number range. -/
private theorem map_val_ofFn_id :
    (List.ofFn (id : Fin n → Fin n)).map Fin.val = List.range n := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    simp

/-- The model's generic path edges on a natural range are its fixed greedy
path edges. -/
private theorem pathEdges_range :
    Model.pathEdges (List.range n) = Model.greedyPathEdges n := by
  apply List.ext_get
  · simp [Model.pathEdges, Model.greedyPathEdges]
  · intro i hleft hright
    simp [Model.pathEdges, Model.greedyPathEdges, Nat.add_comm]

omit [DecidableEq α] in
/-- Canonical labels give exactly the executable path
`0 → 1 → ⋯ → n - 1`. -/
theorem canonicalTerminalPath_of_labels
    {terminal : PathComponent (Fin n) α}
    (hlabels : terminal.labels = List.ofFn id) :
    CanonicalTerminalPath terminal := by
  unfold CanonicalTerminalPath
  rw [hlabels, map_modelEdge_adjacentEdges, map_val_ofFn_id,
    pathEdges_range]

/-- Literal singleton-ending greedy execution satisfies the factor-two bound
whenever the dense encoding and exact certificate corpus cover every
Hamiltonian order for its selected canonical relabelling. -/
theorem literalGreedyRun_factorTwo
    (data : WordInstance α n)
    (shortest : IsShortestCommonSuperstring data)
    (hn : 0 < n)
    (g : Word α)
    (literal : GreedyRun (List.ofFn data.word) [g])
    (coverage :
      ∀ lift : LiteralLift data g,
        RelabelledCaseCertificates lift.canonicalRelabelling) :
    g.length ≤ 2 * data.optimumLength := by
  obtain ⟨lift⟩ := LiteralLift.nonempty_of_literal data g literal
  let result := lift.canonicalRelabelling
  have covered : RelabelledCaseCertificates result := by
    simpa [result] using coverage lift
  have reindexedShortest :
      IsShortestCommonSuperstring result.reindexedData :=
    (CanonicalRunRelabelling.reindexed_shortest_iff result).mpr shortest
  have canonical :
      CanonicalTerminalPath result.reindexedTerminal :=
    canonicalTerminalPath_of_labels result.terminal_labels_canonical
  have bound :
      result.reindexedTerminal.text.length ≤
        2 * result.reindexedData.optimumLength := by
    exact EndToEnd.canonicalLabelledRun_factorTwo
      result.reindexedData result.reindexedTerminal result.chronology
      result.canonicalRun canonical hn reindexedShortest
      covered.encoding covered.certified
  have terminalText :
      result.reindexedTerminal.text = g := by
    calc
      result.reindexedTerminal.text = lift.terminal.text := by
        exact result.terminal_text_preserved
      _ = g := lift.terminal_text
  simpa [terminalText] using bound

end LiteralEndToEnd

end GreedySuperstring
