import GreedySuperstring.ChronologyBridge

/-!
# Constructing chronology alignment from a labelled run

This module proves the path-forest correctness facts needed to construct the
structural `ChronologyAlignment` automatically.  In particular, the model's
executable weak-component test is related to the literal component paths,
and a feasible raw edge is decoded as a last-to-first edge between two
distinct current components.
-/

namespace GreedySuperstring

open GreedySuperstring.Relaxation
open ChronologyBridge

namespace ChronologyConstruction

variable {α : Type u} {n : Nat} [DecidableEq α]

/-! ## Executable weak closure -/

/-- Public spelling of the private closure step used by `Model.weakComponent`.
The equality below is definitional; this duplicate name merely exposes an
induction surface. -/
private def closureStep (n : Nat) (chosen : List Model.Edge)
    (seen : List Nat) : List Nat :=
  (Model.vertices n).filter fun vertex =>
    seen.contains vertex ||
      seen.any fun old => Model.weaklyAdjacent chosen old vertex

private def closureRounds (n : Nat) (chosen : List Model.Edge) :
    Nat → List Nat → List Nat
  | 0, seen => seen
  | rounds + 1, seen =>
      closureRounds n chosen rounds (closureStep n chosen seen)

private theorem weakComponent_eq_closureRounds
    (n : Nat) (chosen : List Model.Edge) (start : Nat) :
    Model.weakComponent n chosen start =
      closureRounds n chosen n [start] := by
  have fold_eq : ∀ (rounds : List Nat) (seen : List Nat),
      rounds.foldl (fun current _ => closureStep n chosen current) seen =
        closureRounds n chosen rounds.length seen := by
    intro rounds
    induction rounds with
    | nil =>
        intro seen
        rfl
    | cons round rounds ih =>
        intro seen
        simp only [List.foldl_cons, List.length_cons, closureRounds]
        exact ih (closureStep n chosen seen)
  change (Model.vertices n).foldl
      (fun current _ => closureStep n chosen current) [start] = _
  rw [fold_eq]
  simp [Model.vertices]

private theorem mem_closureStep_self
    {chosen : List Model.Edge} {seen : List Nat} {vertex : Nat}
    (hlt : vertex < n) (hmem : vertex ∈ seen) :
    vertex ∈ closureStep n chosen seen := by
  simp [closureStep, Model.vertices, hlt, hmem]

private theorem mem_closureStep_of_adjacent
    {chosen : List Model.Edge} {seen : List Nat} {source target : Nat}
    (hlt : target < n) (hsource : source ∈ seen)
    (hadjacent : Model.weaklyAdjacent chosen source target = true) :
    target ∈ closureStep n chosen seen := by
  simp [closureStep, Model.vertices]
  exact ⟨hlt, Or.inr ⟨source, hsource, hadjacent⟩⟩

private theorem closureStep_mono
    {chosen : List Model.Edge} {small large : List Nat}
    (hsub : ∀ vertex ∈ small, vertex ∈ large) :
    ∀ vertex ∈ closureStep n chosen small,
      vertex ∈ closureStep n chosen large := by
  intro vertex hvertex
  simp [closureStep, Model.vertices] at hvertex ⊢
  rcases hvertex with
    ⟨hlt, hself | ⟨source, hsource, hadjacent⟩⟩
  · exact ⟨hlt, Or.inl (hsub vertex hself)⟩
  · exact ⟨hlt, Or.inr ⟨source, hsub source hsource, hadjacent⟩⟩

private theorem closureRounds_mono
    {chosen : List Model.Edge} {small large : List Nat}
    (hsub : ∀ vertex ∈ small, vertex ∈ large) (rounds : Nat) :
    ∀ vertex ∈ closureRounds n chosen rounds small,
      vertex ∈ closureRounds n chosen rounds large := by
  induction rounds generalizing small large with
  | zero => exact hsub
  | succ rounds ih =>
      exact ih (closureStep_mono hsub)

private theorem closureStep_vertices
    {chosen : List Model.Edge} {seen : List Nat} :
    ∀ vertex ∈ closureStep n chosen seen, vertex < n := by
  intro vertex hvertex
  have hrange := (List.mem_filter.mp hvertex).1
  simpa [Model.vertices] using hrange

private theorem closureRounds_vertices
    {chosen : List Model.Edge} {seen : List Nat}
    (hseen : ∀ vertex ∈ seen, vertex < n) (rounds : Nat) :
    ∀ vertex ∈ closureRounds n chosen rounds seen, vertex < n := by
  induction rounds generalizing seen with
  | zero => exact hseen
  | succ rounds ih =>
      exact ih closureStep_vertices

private theorem mem_closureRounds_succ
    {chosen : List Model.Edge} {seen : List Nat} {vertex : Nat}
    (hseen : ∀ item ∈ seen, item < n) {rounds : Nat}
    (hmem : vertex ∈ closureRounds n chosen rounds seen) :
    vertex ∈ closureRounds n chosen (rounds + 1) seen := by
  simp only [closureRounds]
  apply closureRounds_mono (rounds := rounds) _ vertex hmem
  intro item hitem
  exact mem_closureStep_self (hseen item hitem) hitem

private theorem mem_closureRounds_of_le
    {chosen : List Model.Edge} {seen : List Nat} {vertex : Nat}
    (hseen : ∀ item ∈ seen, item < n)
    {small large : Nat} (hle : small ≤ large)
    (hmem : vertex ∈ closureRounds n chosen small seen) :
    vertex ∈ closureRounds n chosen large seen := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simpa
  | succ extra ih =>
      exact mem_closureRounds_succ hseen ih

private theorem closureRounds_succ_end
    (n : Nat) (chosen : List Model.Edge) (rounds : Nat)
    (seen : List Nat) :
    closureRounds n chosen (rounds + 1) seen =
      closureStep n chosen (closureRounds n chosen rounds seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [closureRounds]
      exact ih (closureStep n chosen seen)

private theorem weaklyAdjacent_of_edge_mem
    {chosen : List Model.Edge} {source target : Nat}
    (hmem : ({ src := source, dst := target } : Model.Edge) ∈ chosen) :
    Model.weaklyAdjacent chosen source target = true := by
  simp [Model.weaklyAdjacent]
  exact ⟨{ src := source, dst := target }, hmem,
    Or.inl ⟨rfl, rfl⟩⟩

private theorem weaklyAdjacent_of_edge_mem_reverse
    {chosen : List Model.Edge} {source target : Nat}
    (hmem : ({ src := source, dst := target } : Model.Edge) ∈ chosen) :
    Model.weaklyAdjacent chosen target source = true := by
  simp [Model.weaklyAdjacent]
  exact ⟨{ src := source, dst := target }, hmem,
    Or.inr ⟨rfl, rfl⟩⟩

private theorem labelPath_last_reachable
    {chosen : List Model.Edge} (path : LabelPath (Fin n))
    (seen : List Nat) (hfirst : path.first.val ∈ seen)
    (hedges : ∀ edge ∈ adjacentEdges path.labels,
      modelEdge edge ∈ chosen) :
    path.last.val ∈
      closureRounds n chosen path.rest.length seen := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first seen with
  | nil =>
      exact hfirst
  | cons next rest ih =>
      have hedge : modelEdge (first, next) ∈ chosen :=
        hedges (first, next) (by simp [LabelPath.labels, adjacentEdges])
      have hadjacent :
          Model.weaklyAdjacent chosen first.val next.val = true := by
        exact weaklyAdjacent_of_edge_mem hedge
      have hnext :
          next.val ∈ closureStep n chosen seen :=
        mem_closureStep_of_adjacent next.isLt hfirst hadjacent
      have htail : ∀ edge ∈
          adjacentEdges (LabelPath.mk next rest).labels,
          modelEdge edge ∈ chosen := by
        intro edge hedgeTail
        apply hedges edge
        simpa [LabelPath.labels, adjacentEdges] using
          List.mem_cons_of_mem (first, next) hedgeTail
      change (LabelPath.mk next rest).last.val ∈
        closureRounds n chosen rest.length
          (closureStep n chosen seen)
      exact ih (closureStep n chosen seen) next hnext htail

private theorem labelPath_first_reachable
    {chosen : List Model.Edge} (path : LabelPath (Fin n))
    (seen : List Nat) (hlast : path.last.val ∈ seen)
    (hedges : ∀ edge ∈ adjacentEdges path.labels,
      modelEdge edge ∈ chosen) :
    path.first.val ∈
      closureRounds n chosen path.rest.length seen := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first seen with
  | nil =>
      exact hlast
  | cons next rest ih =>
      have hedge : modelEdge (first, next) ∈ chosen :=
        hedges (first, next) (by simp [LabelPath.labels, adjacentEdges])
      have hadjacent :
          Model.weaklyAdjacent chosen next.val first.val = true := by
        exact weaklyAdjacent_of_edge_mem_reverse hedge
      have htail : ∀ edge ∈
          adjacentEdges (LabelPath.mk next rest).labels,
          modelEdge edge ∈ chosen := by
        intro edge hedgeTail
        apply hedges edge
        simpa [LabelPath.labels, adjacentEdges] using
          List.mem_cons_of_mem (first, next) hedgeTail
      have hnext : next.val ∈
          closureRounds n chosen rest.length seen := by
        exact ih seen next hlast htail
      change first.val ∈
        closureRounds n chosen (rest.length + 1) seen
      rw [closureRounds_succ_end]
      exact mem_closureStep_of_adjacent first.isLt hnext hadjacent

omit [DecidableEq α] in
/-- All labels of one current component lie in one executable weak component
of any chosen-edge list containing its internal adjacent edges. -/
theorem weaklyConnected_first_last
    {chosen : List Model.Edge} (component : PathComponent (Fin n) α)
    (hnodup : component.labels.Nodup)
    (hedges : ∀ edge ∈ adjacentEdges component.labels,
      modelEdge edge ∈ chosen) :
    Model.weaklyConnected n chosen component.first.val
      component.last.val = true := by
  have hreach := labelPath_last_reachable component.path
    [component.first.val] (by simp [PathComponent.first]) hedges
  have hlength : component.path.rest.length ≤ n := by
    have hcard := hnodup.length_le_card
    simp [PathComponent.labels, LabelPath.labels] at hcard
    omega
  have hreachN := mem_closureRounds_of_le
    (n := n) (chosen := chosen)
    (seen := [component.first.val]) (vertex := component.last.val)
    (by
      intro item hitem
      rw [List.mem_singleton] at hitem
      subst item
      exact component.first.isLt)
    hlength hreach
  rw [Model.weaklyConnected, weakComponent_eq_closureRounds]
  simpa using hreachN

omit [DecidableEq α] in
/-- The same internal path is connected in reverse because the model's weak
adjacency test treats every selected directed edge as undirected. -/
theorem weaklyConnected_last_first
    {chosen : List Model.Edge} (component : PathComponent (Fin n) α)
    (hnodup : component.labels.Nodup)
    (hedges : ∀ edge ∈ adjacentEdges component.labels,
      modelEdge edge ∈ chosen) :
    Model.weaklyConnected n chosen component.last.val
      component.first.val = true := by
  have hreach := labelPath_first_reachable component.path
    [component.last.val] (by simp [PathComponent.last]) hedges
  have hlength : component.path.rest.length ≤ n := by
    have hcard := hnodup.length_le_card
    simp [PathComponent.labels, LabelPath.labels] at hcard
    omega
  have hreachN := mem_closureRounds_of_le
    (n := n) (chosen := chosen)
    (seen := [component.last.val]) (vertex := component.first.val)
    (by
      intro item hitem
      rw [List.mem_singleton] at hitem
      subst item
      exact component.last.isLt)
    hlength hreach
  rw [Model.weaklyConnected, weakComponent_eq_closureRounds]
  simpa using hreachN

/-! ## Feasible edges and current components -/

private theorem exists_outgoing_adjacent
    (path : LabelPath (Fin n)) {label : Fin n}
    (hmem : label ∈ path.labels) (hne : label ≠ path.last) :
    ∃ next, (label, next) ∈ adjacentEdges path.labels := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first with
  | nil =>
      have heq : label = first := by
        simpa [LabelPath.labels] using hmem
      subst label
      exact (hne rfl).elim
  | cons next rest ih =>
      rcases List.mem_cons.mp hmem with heq | htail
      · subst label
        exact ⟨next, by simp [LabelPath.labels, adjacentEdges]⟩
      · have hneTail : label ≠ (LabelPath.mk next rest).last := by
          exact hne
        rcases ih next htail hneTail with ⟨after, hedge⟩
        exact ⟨after, by
          simpa [LabelPath.labels, adjacentEdges] using
            List.mem_cons_of_mem (first, next) hedge⟩

private theorem exists_incoming_adjacent
    (path : LabelPath (Fin n)) {label : Fin n}
    (hmem : label ∈ path.labels) (hne : label ≠ path.first) :
    ∃ previous, (previous, label) ∈ adjacentEdges path.labels := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first with
  | nil =>
      have heq : label = first := by
        simpa [LabelPath.labels] using hmem
      exact (hne heq).elim
  | cons next rest ih =>
      rcases List.mem_cons.mp hmem with heq | htail
      · exact (hne heq).elim
      · by_cases heq : label = next
        · subst label
          exact ⟨first, by simp [LabelPath.labels, adjacentEdges]⟩
        · rcases ih next htail heq with ⟨previous, hedge⟩
          exact ⟨previous, by
            simpa [LabelPath.labels, adjacentEdges] using
              List.mem_cons_of_mem (first, next) hedge⟩

omit [DecidableEq α] in
/-- A model-feasible edge is exactly an exposed last-to-first interface
between two distinct current components, provided the component labels cover
all vertices and their internal edges are the already chosen edges. -/
theorem feasibleEdge_realized
    {weight : Fin n → Fin n → Nat}
    {components : List (PathComponent (Fin n) α)}
    {chosenPairs : List (Fin n × Fin n)}
    (state : PathState weight components)
    (hcoverage : List.Perm (componentLabels components) (List.ofFn id))
    (hinternal : List.Perm
      (componentAdjacentEdges components) chosenPairs)
    {candidate : Model.Edge}
    (hfeasible : candidate ∈
      Model.feasibleEdges n (modelChronology chosenPairs)) :
    ∃ (left right : PathComponent (Fin n) α),
      left ∈ components ∧ right ∈ components ∧ left ≠ right ∧
      candidate = modelEdge (left.last, right.first) := by
  have hfeasibleBool := (List.mem_filter.mp hfeasible).2
  simp [Model.feasibleEdge, Model.validEdge] at hfeasibleBool
  rcases hfeasibleBool with
    ⟨⟨⟨⟨⟨hsourceLt, htargetLt⟩, hsourceTarget⟩, hnoSource⟩,
      hnoTarget⟩, hnotConnected⟩
  let source : Fin n := ⟨candidate.src, hsourceLt⟩
  let target : Fin n := ⟨candidate.dst, htargetLt⟩
  have hsourceFlat : source ∈ componentLabels components := by
    apply hcoverage.mem_iff.mpr
    simp
  have htargetFlat : target ∈ componentLabels components := by
    apply hcoverage.mem_iff.mpr
    simp
  change source ∈ components.flatMap PathComponent.labels at hsourceFlat
  change target ∈ components.flatMap PathComponent.labels at htargetFlat
  rcases List.mem_flatMap.mp hsourceFlat with
    ⟨left, hleft, hsourceMem⟩
  rcases List.mem_flatMap.mp htargetFlat with
    ⟨right, hright, htargetMem⟩
  have edge_mem_chosen : ∀
      {component : PathComponent (Fin n) α}, component ∈ components →
      ∀ {edge : Fin n × Fin n}, edge ∈ adjacentEdges component.labels →
        modelEdge edge ∈ modelChronology chosenPairs := by
    intro component hcomponent edge hedge
    have hforest : edge ∈ componentAdjacentEdges components := by
      simp only [componentAdjacentEdges, List.mem_flatMap]
      exact ⟨component, hcomponent, hedge⟩
    have hpairs : edge ∈ chosenPairs :=
      hinternal.mem_iff.mp hforest
    exact List.mem_map_of_mem (f := modelEdge) hpairs
  have hsourceLast : source = left.last := by
    by_contra hne
    rcases exists_outgoing_adjacent left.path hsourceMem hne with
      ⟨next, hedge⟩
    have hchosen := edge_mem_chosen hleft hedge
    exact hnoSource (modelEdge (source, next)) hchosen rfl
  have htargetFirst : target = right.first := by
    by_contra hne
    rcases exists_incoming_adjacent right.path htargetMem hne with
      ⟨previous, hedge⟩
    have hchosen := edge_mem_chosen hright hedge
    exact hnoTarget (modelEdge (previous, target)) hchosen rfl
  have hsourceVal : candidate.src = left.last.val := by
    simpa [source] using congrArg Fin.val hsourceLast
  have htargetVal : candidate.dst = right.first.val := by
    simpa [target] using congrArg Fin.val htargetFirst
  have hdistinct : left ≠ right := by
    intro heq
    subst right
    have hedgesLeft : ∀ edge ∈ adjacentEdges left.labels,
        modelEdge edge ∈ modelChronology chosenPairs := by
      intro edge hedge
      exact edge_mem_chosen hleft hedge
    have hconnected := weaklyConnected_last_first left
      (state.labels_nodup hleft) hedgesLeft
    rw [hsourceVal, htargetVal] at hnotConnected
    rw [hnotConnected] at hconnected
    contradiction
  refine ⟨left, right, hleft, hright, hdistinct, ?_⟩
  rcases candidate with ⟨sourceValue, targetValue⟩
  change sourceValue = left.last.val at hsourceVal
  change targetValue = right.first.val at htargetVal
  subst sourceValue
  subst targetValue
  rfl

/-! ## Locating a labelled step by chronology index -/

private structure GenericRunStepOccurrence
    (weight : Fin n → Fin n → Nat)
    (start final : List (PathComponent (Fin n) α))
    (edges : List (Fin n × Fin n)) where
  before : List (PathComponent (Fin n) α)
  after : List (PathComponent (Fin n) α)
  edge : Fin n × Fin n
  prefixEdges : List (Fin n × Fin n)
  suffixEdges : List (Fin n × Fin n)
  priorRun : LabelledGreedyRun weight start before prefixEdges
  selected : LabelledGreedyStep weight before after edge
  suffix : LabelledGreedyRun weight after final suffixEdges
  edges_eq : edges = prefixEdges ++ edge :: suffixEdges

private theorem genericRunStepOccurrenceAt
    {weight : Fin n → Fin n → Nat}
    {start final : List (PathComponent (Fin n) α)}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun weight start final edges)
    {index : Nat} (hindex : index < edges.length) :
    ∃ occurrence : GenericRunStepOccurrence weight start final edges,
      occurrence.prefixEdges.length = index := by
  induction run with
  | refl =>
      simp at hindex
  | @tail current next priorEdges finalEdge priorRun finalStep ih =>
      by_cases hprior : index < priorEdges.length
      · rcases ih hprior with ⟨occurrence, hlength⟩
        refine ⟨{
          before := occurrence.before
          after := occurrence.after
          edge := occurrence.edge
          prefixEdges := occurrence.prefixEdges
          suffixEdges := occurrence.suffixEdges ++ [finalEdge]
          priorRun := occurrence.priorRun
          selected := occurrence.selected
          suffix := LabelledGreedyRun.tail occurrence.suffix finalStep
          edges_eq := ?_
        }, hlength⟩
        calc
          priorEdges ++ [finalEdge] =
              (occurrence.prefixEdges ++
                occurrence.edge :: occurrence.suffixEdges) ++
                [finalEdge] :=
            congrArg (fun listed => listed ++ [finalEdge])
              occurrence.edges_eq
          _ = occurrence.prefixEdges ++
              occurrence.edge ::
                (occurrence.suffixEdges ++ [finalEdge]) := by
            simp [List.append_assoc]
      · have hlast : index = priorEdges.length := by
          simp only [List.length_append, List.length_singleton] at hindex
          omega
        refine ⟨{
          before := current
          after := next
          edge := finalEdge
          prefixEdges := priorEdges
          suffixEdges := []
          priorRun := priorRun
          selected := finalStep
          suffix := LabelledGreedyRun.refl next
          edges_eq := ?_
        }, hlast.symm⟩
        simp

/-- Every in-range model step has a concrete selected labelled merge at the
same prefix length. -/
theorem runStepOccurrenceAt
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    {index : Nat} (hindex : index < edges.length) :
    ∃ occurrence : RunStepOccurrence data terminal edges,
      occurrence.prefixEdges.length = index := by
  rcases genericRunStepOccurrenceAt run hindex with
    ⟨occurrence, hlength⟩
  exact ⟨{
    before := occurrence.before
    after := occurrence.after
    edge := occurrence.edge
    prefixEdges := occurrence.prefixEdges
    suffixEdges := occurrence.suffixEdges
    priorRun := occurrence.priorRun
    selected := occurrence.selected
    suffix := occurrence.suffix
    edges_eq := occurrence.edges_eq
  }, hlength⟩

/-! ## Decoding generated chronology rows -/

private theorem generatedDominance_in_greedyRows
    {chronology : List Model.Edge} {step : Nat}
    {selected candidate : Model.Edge}
    (generated : PrimalBridge.GeneratedKind n chronology
      (.greedyDominance step selected candidate)) :
    ∃ row ∈ Model.greedyRows n chronology,
      row.kind = .greedyDominance step selected candidate := by
  rcases generated with ⟨row, hrow, hkind⟩
  simp only [Model.inequalityRows, List.mem_append] at hrow
  rcases hrow with ((hcap | htriangle) | hpair) | hgreedy
  · simp [Model.endpointCapRows] at hcap
    rcases hcap with ⟨edge, _, rfl | rfl⟩ <;> contradiction
  · simp [Model.triangleRows] at htriangle
    rcases htriangle with ⟨i, _, j, _, k, _, _, rfl⟩
    contradiction
  · simp [Model.intervalPairRows] at hpair
    rcases hpair with ⟨i, _, j, _, _, rfl⟩
    contradiction
  · exact ⟨row, hgreedy, hkind⟩

private theorem generatedRectangle_in_greedyRows
    {chronology : List Model.Edge} {step : Nat}
    {selected crossA crossB bottom : Model.Edge}
    (generated : PrimalBridge.GeneratedKind n chronology
      (.licensedRectangle step selected crossA crossB bottom)) :
    ∃ row ∈ Model.greedyRows n chronology,
      row.kind = .licensedRectangle step selected crossA crossB bottom := by
  rcases generated with ⟨row, hrow, hkind⟩
  simp only [Model.inequalityRows, List.mem_append] at hrow
  rcases hrow with ((hcap | htriangle) | hpair) | hgreedy
  · simp [Model.endpointCapRows] at hcap
    rcases hcap with ⟨edge, _, rfl | rfl⟩ <;> contradiction
  · simp [Model.triangleRows] at htriangle
    rcases htriangle with ⟨i, _, j, _, k, _, _, rfl⟩
    contradiction
  · simp [Model.intervalPairRows] at hpair
    rcases hpair with ⟨i, _, j, _, _, rfl⟩
    contradiction
  · exact ⟨row, hgreedy, hkind⟩

private theorem decodeDominanceAux
    {chosen chronology : List Model.Edge} {baseStep step : Nat}
    {selected candidate : Model.Edge}
    (hrow : ∃ row ∈ Model.greedyRowsFrom n chosen baseStep chronology,
      row.kind = .greedyDominance step selected candidate) :
    ∃ chosenPrefix suffix,
      chronology = chosenPrefix ++ selected :: suffix ∧
      step = baseStep + chosenPrefix.length ∧
      candidate ∈ Model.feasibleEdges n (chosen ++ chosenPrefix) := by
  induction chronology generalizing chosen baseStep with
  | nil =>
      rcases hrow with ⟨row, hmem, _⟩
      simp at hmem
  | cons head tail ih =>
      rcases hrow with ⟨row, hmem, hkind⟩
      simp only [Model.greedyRowsFrom_cons, List.mem_append] at hmem
      rcases hmem with (hdominance | hrectangle) | htail
      · simp [Model.greedyDominanceRows] at hdominance
        rcases hdominance with
          ⟨found, ⟨hfound, _⟩, rfl⟩
        cases hkind
        exact ⟨[], tail, by simp, by simp, by simpa using hfound⟩
      · simp [Model.licensedRectangleRows] at hrectangle
        rcases hrectangle with
          ⟨u, _, v, _, _, _, rfl⟩
        contradiction
      · rcases ih (chosen := chosen ++ [head])
          (baseStep := baseStep + 1) ⟨row, htail, hkind⟩ with
          ⟨chosenPrefix, suffix, horder, hstep, hcandidate⟩
        refine ⟨head :: chosenPrefix, suffix, ?_, ?_, ?_⟩
        · simp [horder]
        · simp only [List.length_cons]
          omega
        · simpa [List.append_assoc] using hcandidate

private theorem decodeRectangleAux
    {chosen chronology : List Model.Edge} {baseStep step : Nat}
    {selected crossA crossB bottom : Model.Edge}
    (hrow : ∃ row ∈ Model.greedyRowsFrom n chosen baseStep chronology,
      row.kind = .licensedRectangle step selected crossA crossB bottom) :
    ∃ chosenPrefix suffix,
      chronology = chosenPrefix ++ selected :: suffix ∧
      step = baseStep + chosenPrefix.length ∧
      crossA ∈ Model.feasibleEdges n (chosen ++ chosenPrefix) ∧
      crossB ∈ Model.feasibleEdges n (chosen ++ chosenPrefix) := by
  induction chronology generalizing chosen baseStep with
  | nil =>
      rcases hrow with ⟨row, hmem, _⟩
      simp at hmem
  | cons head tail ih =>
      rcases hrow with ⟨row, hmem, hkind⟩
      simp only [Model.greedyRowsFrom_cons, List.mem_append] at hmem
      rcases hmem with (hdominance | hrectangle) | htail
      · simp [Model.greedyDominanceRows] at hdominance
        rcases hdominance with ⟨found, _, rfl⟩
        contradiction
      · simp [Model.licensedRectangleRows] at hrectangle
        rcases hrectangle with
          ⟨u, _, v, _, _, hcontains, rfl⟩
        cases hkind
        exact ⟨[], tail, by simp, by simp,
          by simpa using hcontains.1, by simpa using hcontains.2⟩
      · rcases ih (chosen := chosen ++ [head])
          (baseStep := baseStep + 1) ⟨row, htail, hkind⟩ with
          ⟨chosenPrefix, suffix, horder, hstep, hcrossA, hcrossB⟩
        refine ⟨head :: chosenPrefix, suffix, ?_, ?_, ?_, ?_⟩
        · simp [horder]
        · simp only [List.length_cons]
          omega
        · simpa [List.append_assoc] using hcrossA
        · simpa [List.append_assoc] using hcrossB

/-- Every generated comparison identifies its exact chronology position and
is feasible against the model prefix at that position. -/
theorem requiredComparison_decoded
    {chronology : List Model.Edge} {step : Nat}
    {selected candidate : Model.Edge}
    (required : RequiredComparison n chronology step selected candidate) :
    ∃ chosenPrefix suffix,
      chronology = chosenPrefix ++ selected :: suffix ∧
      chosenPrefix.length = step ∧
      candidate ∈ Model.feasibleEdges n chosenPrefix := by
  cases required with
  | dominance generated =>
      have hrow := generatedDominance_in_greedyRows generated
      rw [Model.greedyRows_eq_from] at hrow
      rcases decodeDominanceAux hrow with
        ⟨chosenPrefix, suffix, horder, hstep, hcandidate⟩
      exact ⟨chosenPrefix, suffix, horder, by omega,
        by simpa using hcandidate⟩
  | rectangleA generated =>
      have hrow := generatedRectangle_in_greedyRows generated
      rw [Model.greedyRows_eq_from] at hrow
      rcases decodeRectangleAux hrow with
        ⟨chosenPrefix, suffix, horder, hstep, hcrossA, _⟩
      exact ⟨chosenPrefix, suffix, horder, by omega,
        by simpa using hcrossA⟩
  | rectangleB generated =>
      have hrow := generatedRectangle_in_greedyRows generated
      rw [Model.greedyRows_eq_from] at hrow
      rcases decodeRectangleAux hrow with
        ⟨chosenPrefix, suffix, horder, hstep, _, hcrossB⟩
      exact ⟨chosenPrefix, suffix, horder, by omega,
        by simpa using hcrossB⟩

/-! ## Automatic chronology alignment -/

private theorem decomposition_unique
    {β : Type v} {whole left₁ left₂ right₁ right₂ : List β} {a b : β}
    (h₁ : whole = left₁ ++ a :: right₁)
    (h₂ : whole = left₂ ++ b :: right₂)
    (hlength : left₁.length = left₂.length) :
    left₁ = left₂ ∧ a = b := by
  have hwhole : left₁ ++ a :: right₁ = left₂ ++ b :: right₂ :=
    h₁.symm.trans h₂
  have hleft : left₁ = left₂ := by
    calc
      left₁ = (left₁ ++ a :: right₁).take left₁.length := by simp
      _ = (left₂ ++ b :: right₂).take left₁.length :=
        congrArg (List.take left₁.length) hwhole
      _ = left₂ := by rw [hlength]; simp
  subst left₂
  have htail : a :: right₁ = b :: right₂ :=
    List.append_cancel_left hwhole
  exact ⟨rfl, (List.cons.inj htail).1⟩

omit [DecidableEq α] in
private theorem initialPathState
    (data : WordInstance α n) :
    PathState data.overlap
      (initialComponents data.word (List.ofFn id)) := by
  apply PathState.initial
  · simpa [List.map_ofFn, Function.comp_def] using data.reduced
  · exact data.maximum

/-- Every labelled greedy run is structurally aligned with every comparison
emitted by the executable chronology-row generator.  No separate chronology
validity, row inequality, or alignment hypothesis is required. -/
theorem chronologyAlignment_of_run
    {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges) :
    ChronologyAlignment data terminal edges where
  run := run
  comparison := by
    intro step selected candidate required
    rcases requiredComparison_decoded required with
      ⟨chosenPrefix, generatedSuffix, hgenerated, hprefixLength,
        hcandidateFeasible⟩
    have hstepModel : step < (modelChronology edges).length := by
      rw [hgenerated]
      simp only [List.length_append, List.length_cons]
      omega
    have hstepEdges : step < edges.length := by
      simpa [modelChronology] using hstepModel
    rcases runStepOccurrenceAt run hstepEdges with
      ⟨occurrence, hoccurLength⟩
    have hrunChronology :
        modelChronology edges =
          modelChronology occurrence.prefixEdges ++
            modelEdge occurrence.edge ::
              modelChronology occurrence.suffixEdges := by
      calc
        modelChronology edges =
            modelChronology
              (occurrence.prefixEdges ++ occurrence.edge ::
                occurrence.suffixEdges) :=
          congrArg modelChronology occurrence.edges_eq
        _ = modelChronology occurrence.prefixEdges ++
              modelEdge occurrence.edge ::
                modelChronology occurrence.suffixEdges := by
          simp [modelChronology, List.map_append]
    have hprefixModelLength :
        chosenPrefix.length =
          (modelChronology occurrence.prefixEdges).length := by
      simp only [modelChronology, List.length_map]
      omega
    rcases decomposition_unique hgenerated hrunChronology
        hprefixModelLength with ⟨hprefixEq, hselectedEq⟩
    have hstate :=
      (occurrence.priorRun.invariant (initialPathState data)).final_state
    have hcoverage :
        List.Perm (componentLabels occurrence.before) (List.ofFn id) := by
      simpa using
        (occurrence.priorRun.invariant
          (initialPathState data)).labels_perm
    have hinternal :
        List.Perm (componentAdjacentEdges occurrence.before)
          occurrence.prefixEdges := by
      simpa using occurrence.priorRun.componentAdjacentEdges_perm
    have hcandidateAtRunPrefix :
        candidate ∈ Model.feasibleEdges n
          (modelChronology occurrence.prefixEdges) := by
      rw [← hprefixEq]
      exact hcandidateFeasible
    rcases feasibleEdge_realized hstate hcoverage hinternal
        hcandidateAtRunPrefix with
      ⟨candidateLeft, candidateRight, hleft, hright, hdistinct,
        hcandidateEq⟩
    exact ⟨{
      occurrence := occurrence
      candidateLeft := candidateLeft
      candidateRight := candidateRight
      candidateLeft_mem := hleft
      candidateRight_mem := hright
      candidate_distinct := hdistinct
      step_eq := hoccurLength.symm
      selected_eq := hselectedEq
      candidate_eq := hcandidateEq
    }⟩

end ChronologyConstruction

end GreedySuperstring
