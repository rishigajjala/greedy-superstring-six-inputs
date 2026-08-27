import GreedySuperstring.RunLabelling
import GreedySuperstring.PrimalBridge

/-!
# From labelled greedy runs to LP chronology hypotheses

This module isolates the structural alignment between a literal labelled run
and the executable chronology rows.  The alignment contains no numerical
inequality: it says only which current components realize every comparison
requested by a generated dominance or rectangle row.  Path-state endpoint
interfaces and the selected step's global maximality then prove all of the
`PrimalBridge.ChronologyHypotheses` inequalities.
-/

namespace GreedySuperstring

open GreedySuperstring.Relaxation

namespace ChronologyBridge

variable {α : Type u} {n : Nat} [DecidableEq α]

/-- Erase the `Fin n` bounds from one original-label edge. -/
def modelEdge (edge : Fin n × Fin n) : Model.Edge where
  src := edge.1.val
  dst := edge.2.val

/-- The executable chronology carried by a labelled run. -/
def modelChronology (edges : List (Fin n × Fin n)) : List Model.Edge :=
  edges.map modelEdge

omit [DecidableEq α] in
theorem edgeWeight_modelEdge (data : WordInstance α n)
    {source target : Fin n} (hne : source ≠ target) :
    PrimalBridge.edgeWeight data (modelEdge (source, target)) =
      data.overlap source target := by
  have hval : source.val ≠ target.val := by
    intro h
    exact hne (Fin.ext h)
  simp [PrimalBridge.edgeWeight, modelEdge, source.isLt, target.isLt, hval]

private theorem labelPath_last_mem (path : LabelPath (Fin n)) :
    path.last ∈ path.labels := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first with
  | nil =>
      change first ∈ [first]
      simp
  | cons next rest ih =>
      change (LabelPath.mk next rest).last ∈ first :: next :: rest
      exact List.mem_cons_of_mem first (ih next)

omit [DecidableEq α] in
private theorem last_ne_first
    {weight : Fin n → Fin n → Nat}
    {components : List (PathComponent (Fin n) α)}
    (state : PathState weight components)
    {left right : PathComponent (Fin n) α}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) :
    left.last ≠ right.first := by
  intro heq
  change left.path.last = right.path.first at heq
  have hdisjoint := state.labels_disjoint hleft hright hne
  apply hdisjoint (labelPath_last_mem left.path)
  rw [heq]
  simp [PathComponent.labels, LabelPath.labels]

/-- One selected labelled step together with its position in a complete run.
The edge-list equation records chronological, rather than proof-term, order. -/
structure RunStepOccurrence
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n)) where
  before : List (PathComponent (Fin n) α)
  after : List (PathComponent (Fin n) α)
  edge : Fin n × Fin n
  prefixEdges : List (Fin n × Fin n)
  suffixEdges : List (Fin n × Fin n)
  priorRun : LabelledGreedyRun data.overlap
    (initialComponents data.word (List.ofFn id)) before prefixEdges
  selected : LabelledGreedyStep data.overlap before after edge
  suffix : LabelledGreedyRun data.overlap after [terminal] suffixEdges
  edges_eq : edges = prefixEdges ++ edge :: suffixEdges

/-- Structural realization of one model comparison by two distinct current
components at the labelled step selecting `selected`. -/
structure AlignedComparison
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n))
    (step : Nat) (selected candidate : Model.Edge) where
  occurrence : RunStepOccurrence data terminal edges
  candidateLeft : PathComponent (Fin n) α
  candidateRight : PathComponent (Fin n) α
  candidateLeft_mem : candidateLeft ∈ occurrence.before
  candidateRight_mem : candidateRight ∈ occurrence.before
  candidate_distinct : candidateLeft ≠ candidateRight
  step_eq : step = occurrence.prefixEdges.length
  selected_eq : selected = modelEdge occurrence.edge
  candidate_eq : candidate =
    modelEdge (candidateLeft.last, candidateRight.first)

/-- Comparisons whose semantic validity is required by generated greedy rows.
A rectangle contributes its two cross edges and no bottom-edge assumption. -/
inductive RequiredComparison (n : Nat) (chronology : List Model.Edge)
    (step : Nat) (selected candidate : Model.Edge) : Prop where
  | dominance :
      PrimalBridge.GeneratedKind n chronology
        (.greedyDominance step selected candidate) →
      RequiredComparison n chronology step selected candidate
  | rectangleA {crossB bottom : Model.Edge} :
      PrimalBridge.GeneratedKind n chronology
        (.licensedRectangle step selected candidate crossB bottom) →
      RequiredComparison n chronology step selected candidate
  | rectangleB {crossA bottom : Model.Edge} :
      PrimalBridge.GeneratedKind n chronology
        (.licensedRectangle step selected crossA candidate bottom) →
      RequiredComparison n chronology step selected candidate

/-- Exact non-numerical alignment boundary between a labelled run and the
row generator. -/
structure ChronologyAlignment
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n)) : Prop where
  run : LabelledGreedyRun data.overlap
    (initialComponents data.word (List.ofFn id)) [terminal] edges
  comparison : ∀ {step : Nat} {selected candidate : Model.Edge},
    RequiredComparison n (modelChronology edges) step selected candidate →
      Nonempty (AlignedComparison data terminal edges step selected candidate)

omit [DecidableEq α] in
private theorem initialPathState (data : WordInstance α n) :
    PathState data.overlap
      (initialComponents data.word (List.ofFn id)) := by
  apply PathState.initial
  · simpa [List.map_ofFn, Function.comp_def] using data.reduced
  · exact data.maximum

namespace AlignedComparison

/-- Global maximality at the aligned selected step dominates the candidate's
exact endpoint-interface overlap. -/
theorem edgeWeight_le
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)} {step : Nat}
    {selected candidate : Model.Edge}
    (aligned : AlignedComparison data terminal edges step selected candidate) :
    PrimalBridge.edgeWeight data candidate ≤
      PrimalBridge.edgeWeight data selected := by
  rcases aligned with
    ⟨occurrence, candidateLeft, candidateRight, hcandidateLeft,
      hcandidateRight, hcandidateDistinct, hstepEq, hselectedEq,
      hcandidateEq⟩
  rcases occurrence with
    ⟨before, after, selectedEdge, prefixEdges, suffixEdges,
      priorRun, selectedStep, suffix, hedges⟩
  have state := (priorRun.invariant (initialPathState data)).final_state
  cases selectedStep with
  | merge left right k hleft hright hdistinct hoverlap hglobal =>
      have hselectedLabels : left.last ≠ right.first :=
        last_ne_first state hleft hright hdistinct
      have hcandidateLabels :
          candidateLeft.last ≠ candidateRight.first :=
        last_ne_first state hcandidateLeft hcandidateRight
          hcandidateDistinct
      have hcandidateMax :=
        state.interface hcandidateLeft hcandidateRight hcandidateDistinct
      have hcandidateBound :
          data.overlap candidateLeft.last candidateRight.first ≤ k :=
        hglobal (PathState.mem_componentWords hcandidateLeft)
          (PathState.mem_componentWords hcandidateRight)
          (state.text_ne hcandidateLeft hcandidateRight hcandidateDistinct)
          _ hcandidateMax.1
      have hselectedWeight :
          k = data.overlap left.last right.first :=
        state.selectedOverlap_eq hleft hright hdistinct hoverlap hglobal
      subst selected
      subst candidate
      rw [edgeWeight_modelEdge data hcandidateLabels,
        edgeWeight_modelEdge data hselectedLabels]
      exact hcandidateBound.trans_eq hselectedWeight

end AlignedComparison

namespace ChronologyAlignment

/-- A structurally aligned labelled run supplies exactly the chronology facts
consumed by the semantic primal construction. -/
theorem chronologyHypotheses
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (alignment : ChronologyAlignment data terminal edges) :
    PrimalBridge.ChronologyHypotheses data (modelChronology edges) where
  dominance := by
    intro step selected candidate generated
    rcases alignment.comparison
      (RequiredComparison.dominance generated) with ⟨aligned⟩
    exact aligned.edgeWeight_le
  rectangleCrossCaps := by
    intro step selected crossA crossB bottom generated
    rcases alignment.comparison
      (RequiredComparison.rectangleA generated) with ⟨alignedA⟩
    rcases alignment.comparison
      (RequiredComparison.rectangleB generated) with ⟨alignedB⟩
    exact ⟨alignedA.edgeWeight_le, alignedB.edgeWeight_le⟩

end ChronologyAlignment

/-- The terminal label path is canonical at the exact executable edge level
used by `Model.greedyObjective`.  This formulation also covers the empty and
singleton cases without a separate nonemptiness convention. -/
def CanonicalTerminalPath (terminal : PathComponent (Fin n) α) : Prop :=
  (adjacentEdges terminal.labels).map modelEdge =
    Model.greedyPathEdges n

private theorem canonicalEdge_valid {edge : Model.Edge}
    (hmem : edge ∈ Model.greedyPathEdges n) :
    PrimalBridge.EdgeValid n edge := by
  rcases List.mem_map.mp hmem with ⟨i, hi, rfl⟩
  have hi' := List.mem_range.mp hi
  change i < n ∧ i + 1 < n ∧ i ≠ i + 1
  omega

omit [DecidableEq α] in
private theorem selectedWeight_eq_modelWeights
    (data : WordInstance α n) {edges : List (Fin n × Fin n)}
    (hvalid : ∀ edge ∈ edges,
      PrimalBridge.EdgeValid n (modelEdge edge)) :
    selectedWeight data.overlap edges =
      ((modelChronology edges).map
        (PrimalBridge.edgeWeight data)).sum := by
  unfold selectedWeight modelChronology
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      have hedgeValid := hvalid edge (by simp)
      have hne : edge.1 ≠ edge.2 := by
        intro heq
        apply hedgeValid.2.2
        simp [modelEdge, heq]
      simp only [List.map_cons, List.sum_cons]
      rw [edgeWeight_modelEdge data hne]
      congr 1
      exact ih (by
        intro other hother
        exact hvalid other (by simp [hother]))

omit [DecidableEq α] in
private theorem totalOriginalLength_eq_totalInputLength
    (data : WordInstance α n) :
    totalOriginalLength data.word (List.ofFn id) =
      data.totalInputLength := by
  simp [totalOriginalLength, WordInstance.totalInputLength,
    WordInstance.inputLength, List.map_ofFn, Function.comp_def]

namespace ChronologyAlignment

/-- When the terminal label path is the canonical path used by the model,
the dense primal's `greedyLength` is exactly the literal greedy output
length.  The proof uses only run telescoping and the permutation between
chronological merge edges and terminal adjacent edges. -/
theorem greedyLength_eq_terminal_length
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (alignment : ChronologyAlignment data terminal edges)
    (hcanonical : CanonicalTerminalPath terminal) :
    PrimalBridge.greedyLength data = (terminal.text.length : Int) := by
  have hlabels :
      (List.ofFn (id : Fin n → Fin n)).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hreduced :
      Reduced ((List.ofFn (id : Fin n → Fin n)).map data.word) := by
    simpa [List.map_ofFn, Function.comp_def] using data.reduced
  have terminalResult :=
    alignment.run.terminalPath hlabels hreduced data.maximum
  have edgePerm :
      List.Perm edges (adjacentEdges terminal.labels) :=
    alignment.run.edges_perm_adjacentEdges
  have chronologyPerm :
      List.Perm (modelChronology edges) (Model.greedyPathEdges n) := by
    unfold modelChronology
    have mapped := edgePerm.map modelEdge
    rw [hcanonical] at mapped
    exact mapped
  have hvalid : ∀ edge ∈ edges,
      PrimalBridge.EdgeValid n (modelEdge edge) := by
    intro edge hedge
    apply canonicalEdge_valid
    apply chronologyPerm.mem_iff.mp
    exact List.mem_map_of_mem (f := modelEdge) hedge
  have hselectedModel := selectedWeight_eq_modelWeights data hvalid
  have hmodelSum :=
    (chronologyPerm.map (PrimalBridge.edgeWeight data)).sum_eq
  have hselectedCanonical :
      selectedWeight data.overlap edges =
        PrimalBridge.canonicalOverlapWeight data := by
    calc
      selectedWeight data.overlap edges =
          ((modelChronology edges).map
            (PrimalBridge.edgeWeight data)).sum := hselectedModel
      _ = ((Model.greedyPathEdges n).map
            (PrimalBridge.edgeWeight data)).sum := hmodelSum
      _ = PrimalBridge.canonicalOverlapWeight data := rfl
  have hlengthNat :
      terminal.text.length + PrimalBridge.canonicalOverlapWeight data =
        data.totalInputLength := by
    calc
      terminal.text.length + PrimalBridge.canonicalOverlapWeight data =
          terminal.text.length + selectedWeight data.overlap edges := by
            rw [hselectedCanonical]
      _ = totalOriginalLength data.word (List.ofFn id) :=
        terminalResult.rendered_length_add
      _ = data.totalInputLength :=
        totalOriginalLength_eq_totalInputLength data
  have hlengthInt :
      (terminal.text.length : Int) +
          PrimalBridge.canonicalOverlapWeight data =
        data.totalInputLength := by
    exact_mod_cast hlengthNat
  unfold PrimalBridge.greedyLength
  omega

end ChronologyAlignment

end ChronologyBridge

end GreedySuperstring
