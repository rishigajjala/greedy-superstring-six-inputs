import GreedySuperstring.PathRun

/-!
# Reconstructing labels from literal greedy runs

The literal `GreedyRun` relation retains the selected words, overlap, and
global-maximality proof at every step.  This module uses those witnesses to
reconstruct corresponding labelled components, producing a
`LabelledGreedyRun` whose underlying literal run is the given execution.  It
also identifies the recorded merge edges, up to permutation, with the
adjacent edges of the terminal label path.
-/

namespace GreedySuperstring

section

variable {ι : Type u} {α : Type v}

/-- Consecutive directed edges of an ordinary label list. -/
def adjacentEdges : List ι → List (ι × ι)
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      (first, second) :: adjacentEdges (second :: rest)

/-- All internal adjacent edges already present in a component forest. -/
def componentAdjacentEdges
    (components : List (PathComponent ι α)) : List (ι × ι) :=
  components.flatMap fun component => adjacentEdges component.labels

private theorem labelPath_last_nil (first : ι) :
    (LabelPath.mk first []).last = first := rfl

private theorem labelPath_last_cons (first next : ι) (rest : List ι) :
    (LabelPath.mk first (next :: rest)).last =
      (LabelPath.mk next rest).last := rfl

private theorem adjacentEdges_labelPath_append
    (left right : LabelPath ι) :
    adjacentEdges (left.labels ++ right.labels) =
      adjacentEdges left.labels ++ [(left.last, right.first)] ++
        adjacentEdges right.labels := by
  cases left with
  | mk first rest =>
      induction rest generalizing first with
      | nil =>
          simp [LabelPath.labels, labelPath_last_nil, adjacentEdges]
      | cons next rest ih =>
          simpa [LabelPath.labels, labelPath_last_cons, adjacentEdges,
            List.append_assoc] using ih (first := next)

theorem adjacentEdges_component_merge
    (left right : PathComponent ι α) (k : Nat) :
    adjacentEdges (left.merge right k).labels =
      adjacentEdges left.labels ++ [(left.last, right.first)] ++
        adjacentEdges right.labels := by
  rw [PathComponent.labels_merge]
  exact adjacentEdges_labelPath_append left.path right.path

@[simp] theorem componentAdjacentEdges_singleton
    (component : PathComponent ι α) :
    componentAdjacentEdges [component] = adjacentEdges component.labels := by
  simp [componentAdjacentEdges]

@[simp] theorem componentAdjacentEdges_initialComponents
    (original : ι → Word α) (labels : List ι) :
    componentAdjacentEdges (initialComponents original labels) = [] := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      change adjacentEdges [label] ++
        componentAdjacentEdges (initialComponents original labels) = []
      simp [adjacentEdges, ih]

variable [DecidableEq ι] [DecidableEq α]

/-- One component replacement adds exactly its selected endpoint edge to the
forest's internal adjacent-edge multiset. -/
theorem componentAdjacentEdges_replaceComponents
    {components : List (PathComponent ι α)}
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) :
    List.Perm
      (componentAdjacentEdges (replaceComponents components left right k))
      ((left.last, right.first) :: componentAdjacentEdges components) := by
  have hright' : right ∈ components.erase left :=
    (List.mem_erase_of_ne hne.symm).2 hright
  have hcomponents :
      List.Perm components
        (left :: right :: (components.erase left).erase right) :=
    (List.perm_cons_erase hleft).trans
      ((List.perm_cons_erase hright').cons left)
  have hold :
      List.Perm (componentAdjacentEdges components)
        (componentAdjacentEdges (left :: right ::
          (components.erase left).erase right)) := by
    exact hcomponents.flatMap
      (fun component _ => List.Perm.refl (adjacentEdges component.labels))
  have hmove :
      List.Perm
        (componentAdjacentEdges (replaceComponents components left right k))
        ((left.last, right.first) ::
          componentAdjacentEdges (left :: right ::
            (components.erase left).erase right)) := by
    simp only [componentAdjacentEdges, replaceComponents, List.flatMap_cons]
    rw [adjacentEdges_component_merge]
    simpa only [List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
        (List.perm_middle (l₁ := adjacentEdges left.labels)
          (a := (left.last, right.first))
          (l₂ := adjacentEdges right.labels ++
            List.flatMap (fun component => adjacentEdges component.labels)
              ((components.erase left).erase right)))
  exact hmove.trans (hold.symm.cons (left.last, right.first))

namespace LabelledGreedyStep

/-- A labelled merge inserts exactly its selected endpoint edge into the
forest's internal adjacent-edge multiset. -/
theorem componentAdjacentEdges_perm
    {weight : ι → ι → Nat}
    {before after : List (PathComponent ι α)} {edge : ι × ι}
    (step : LabelledGreedyStep weight before after edge) :
    List.Perm (componentAdjacentEdges after)
      (edge :: componentAdjacentEdges before) := by
  cases step with
  | merge left right k hleft hright hne _ _ =>
      exact componentAdjacentEdges_replaceComponents hleft hright hne

/-- Every legal literal step out of a path state has a labelled-component
lift.  The result also exposes the next path state and exact word-list
alignment, making it suitable as the induction step for whole runs. -/
theorem exists_of_literal
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    {nextWords : List (Word α)}
    (state : PathState weight components)
    (step : GreedyStep (componentWords components) nextWords) :
    ∃ (nextComponents : List (PathComponent ι α)) (edge : ι × ι),
      LabelledGreedyStep weight components nextComponents edge ∧
      PathState weight nextComponents ∧
      componentWords nextComponents = nextWords := by
  rcases step with
    ⟨leftWord, rightWord, k, hleftWord, hrightWord, hwordNe,
      hoverlap, hglobal, hnextWords⟩
  rcases List.mem_map.mp hleftWord with ⟨left, hleft, hleftText⟩
  rcases List.mem_map.mp hrightWord with ⟨right, hright, hrightText⟩
  subst leftWord
  subst rightWord
  have hne : left ≠ right := by
    intro heq
    subst right
    exact hwordNe rfl
  have update := state.update hleft hright hne hoverlap hglobal
  refine ⟨replaceComponents components left right k,
    (left.last, right.first),
    LabelledGreedyStep.merge left right k hleft hright hne hoverlap hglobal,
    update.next_state, ?_⟩
  exact update.words_eq.trans hnextWords.symm

end LabelledGreedyStep

namespace LabelledGreedyRun

/-- Strong induction-ready completeness: any literal run starting from the
texts of a valid component state can be lifted to a labelled run with exactly
the requested terminal word list. -/
theorem exists_of_literal
    {weight : ι → ι → Nat}
    {startWords finalWords : List (Word α)}
    {startComponents : List (PathComponent ι α)}
    (run : GreedyRun startWords finalWords)
    (startState : PathState weight startComponents)
    (startWords_eq : componentWords startComponents = startWords) :
    ∃ (finalComponents : List (PathComponent ι α))
        (edges : List (ι × ι)),
      LabelledGreedyRun weight startComponents finalComponents edges ∧
      componentWords finalComponents = finalWords := by
  induction run generalizing startComponents with
  | refl =>
      exact ⟨startComponents, [], LabelledGreedyRun.refl startComponents,
        startWords_eq⟩
  | tail priorRun literalStep ih =>
      rcases ih startState startWords_eq with
        ⟨middleComponents, edges, labelledPrefix, hmiddleWords⟩
      have middleState := (labelledPrefix.invariant startState).final_state
      rw [← hmiddleWords] at literalStep
      rcases LabelledGreedyStep.exists_of_literal middleState literalStep with
        ⟨finalComponents, edge, labelledStep, _, hfinalWords⟩
      exact ⟨finalComponents, edges ++ [edge],
        LabelledGreedyRun.tail labelledPrefix labelledStep, hfinalWords⟩

/-- The selected edges of a run, followed by the forest's initial internal
edges, are precisely the final forest's internal adjacent edges as a
multiset. -/
theorem componentAdjacentEdges_perm
    {weight : ι → ι → Nat}
    {start final : List (PathComponent ι α)}
    {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight start final edges) :
    List.Perm (componentAdjacentEdges final)
      (edges ++ componentAdjacentEdges start) := by
  induction run with
  | refl =>
      simp
  | tail run step ih =>
      refine step.componentAdjacentEdges_perm.trans ((ih.cons _).trans ?_)
      simpa only [List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using
          (List.perm_middle (l₁ := _) (a := _) (l₂ := _)).symm

/-- For a run from singleton components to one terminal component, the
chronological selected-edge list is a permutation of the terminal label
path's adjacent-edge list. -/
theorem edges_perm_adjacentEdges
    {original : ι → Word α} {weight : ι → ι → Nat}
    {labels : List ι} {terminal : PathComponent ι α}
    {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight (initialComponents original labels)
      [terminal] edges) :
    List.Perm edges (adjacentEdges terminal.labels) := by
  have hforest := run.componentAdjacentEdges_perm
  simpa only [componentAdjacentEdges_singleton,
    componentAdjacentEdges_initialComponents, List.append_nil] using
      hforest.symm

end LabelledGreedyRun

omit [DecidableEq ι] [DecidableEq α] in
private theorem exists_component_of_words_singleton
    {components : List (PathComponent ι α)} {word : Word α}
    (hwords : componentWords components = [word]) :
    ∃ component : PathComponent ι α,
      components = [component] ∧ component.text = word := by
  cases components with
  | nil => simp [componentWords] at hwords
  | cons component rest =>
      cases rest with
      | nil =>
          refine ⟨component, rfl, ?_⟩
          simpa [componentWords] using hwords
      | cons other rest =>
          simp [componentWords] at hwords

/-- Reverse labelling for a singleton-ending literal run. -/
theorem exists_labelled_terminal_of_literal
    {original : ι → Word α} {weight : ι → ι → Nat}
    {labels : List ι} {word : Word α}
    (hreduced : Reduced (labels.map original))
    (htable : OriginalMaxOverlapTable original weight)
    (run : GreedyRun (labels.map original) [word]) :
    ∃ (terminal : PathComponent ι α) (edges : List (ι × ι)),
      LabelledGreedyRun weight (initialComponents original labels)
        [terminal] edges ∧
      terminal.text = word := by
  have startState := PathState.initial hreduced htable
  have hstart :
      componentWords (initialComponents original labels) = labels.map original :=
    componentWords_initialComponents original labels
  rcases LabelledGreedyRun.exists_of_literal run startState hstart with
    ⟨finalComponents, edges, labelledRun, hfinalWords⟩
  rcases exists_component_of_words_singleton hfinalWords with
    ⟨terminal, rfl, hterminalText⟩
  exact ⟨terminal, edges, labelledRun, hterminalText⟩

/-- Full reverse-labelling closure: every singleton-ending literal greedy run
from the reduced original family has a labelled chronology to which
`LabelledGreedyRun.terminalPath` applies. -/
theorem terminalPath_of_literal
    {original : ι → Word α} {weight : ι → ι → Nat}
    {labels : List ι} {word : Word α}
    (hlabels : labels.Nodup)
    (hreduced : Reduced (labels.map original))
    (htable : OriginalMaxOverlapTable original weight)
    (run : GreedyRun (labels.map original) [word]) :
    ∃ (terminal : PathComponent ι α) (edges : List (ι × ι)),
      terminal.text = word ∧
      LabelledGreedyRun weight (initialComponents original labels)
        [terminal] edges ∧
      List.Perm edges (adjacentEdges terminal.labels) ∧
      TerminalPathResult original weight labels terminal edges := by
  rcases exists_labelled_terminal_of_literal hreduced htable run with
    ⟨terminal, edges, labelledRun, hterminalText⟩
  exact ⟨terminal, edges, hterminalText, labelledRun,
    labelledRun.edges_perm_adjacentEdges,
    labelledRun.terminalPath hlabels hreduced htable⟩

end

end GreedySuperstring
