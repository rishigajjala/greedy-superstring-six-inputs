import GreedySuperstring.PathState
import Mathlib.Data.List.Perm.Basic

/-!
# Labelled greedy runs

This module initializes the original-label path-state invariant and iterates
its one-step update.  A run records the original endpoint edge selected at
each merge, which makes both label conservation and the final telescoping
length identity explicit.
-/

namespace GreedySuperstring

section Initial

variable {ι : Type u} {α : Type v}

namespace PathComponent

/-- The initial component attached to one original label. -/
def singleton (original : ι → Word α) (label : ι) : PathComponent ι α where
  path := ⟨label, []⟩
  text := original label

@[simp] theorem labels_singleton (original : ι → Word α) (label : ι) :
    (singleton original label).labels = [label] := rfl

@[simp] theorem first_singleton (original : ι → Word α) (label : ι) :
    (singleton original label).first = label := rfl

@[simp] theorem last_singleton (original : ι → Word α) (label : ι) :
    (singleton original label).last = label := rfl

@[simp] theorem text_singleton (original : ι → Word α) (label : ι) :
    (singleton original label).text = original label := rfl

end PathComponent

/-- Initial singleton components in the supplied finite label order. -/
def initialComponents (original : ι → Word α) (labels : List ι) :
    List (PathComponent ι α) :=
  labels.map (PathComponent.singleton original)

/-- All original labels currently carried by a component forest. -/
def componentLabels (components : List (PathComponent ι α)) : List ι :=
  components.flatMap PathComponent.labels

/-- Sum of the lengths of the indexed original words. -/
def totalOriginalLength (original : ι → Word α) (labels : List ι) : Nat :=
  (labels.map fun label => (original label).length).sum

@[simp] theorem componentWords_singleton (component : PathComponent ι α) :
    componentWords [component] = [component.text] := rfl

@[simp] theorem componentLabels_singleton (component : PathComponent ι α) :
    componentLabels [component] = component.labels := by
  simp [componentLabels]

@[simp] theorem renderedLength_singleton (component : PathComponent ι α) :
    renderedLength [component] = component.text.length := by
  simp [renderedLength]

@[simp] theorem componentWords_initialComponents
    (original : ι → Word α) (labels : List ι) :
    componentWords (initialComponents original labels) = labels.map original := by
  simp [componentWords, initialComponents]

@[simp] theorem componentLabels_initialComponents
    (original : ι → Word α) (labels : List ι) :
    componentLabels (initialComponents original labels) = labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      change [label] ++ componentLabels (initialComponents original labels) =
        label :: labels
      simp [ih]

@[simp] theorem renderedLength_initialComponents
    (original : ι → Word α) (labels : List ι) :
    renderedLength (initialComponents original labels) =
      totalOriginalLength original labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp [renderedLength, initialComponents, totalOriginalLength] at ih ⊢
      exact ih

namespace PathState

/-- The exact original maximum-overlap table initializes every endpoint
interface between distinct singleton components. -/
theorem initial
    {original : ι → Word α} {weight : ι → ι → Nat} {labels : List ι}
    (hreduced : Reduced (labels.map original))
    (htable : OriginalMaxOverlapTable original weight) :
    PathState weight (initialComponents original labels) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hreduced
  · intro component hcomponent
    rcases List.mem_map.mp hcomponent with ⟨label, _, rfl⟩
    simp
  · intro left hleft right hright hne
    rcases List.mem_map.mp hleft with ⟨i, _, rfl⟩
    rcases List.mem_map.mp hright with ⟨j, _, rfl⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hne rfl
    simp [hij.symm]
  · intro left hleft right hright hne
    rcases List.mem_map.mp hleft with ⟨i, _, rfl⟩
    rcases List.mem_map.mp hright with ⟨j, _, rfl⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hne rfl
    simpa using htable hij

end PathState

end Initial

section Replacement

variable {ι : Type u} {α : Type v} [DecidableEq ι] [DecidableEq α]

/-- Replacing two components by their concatenated component preserves the
multiset of original labels. -/
theorem componentLabels_replaceComponents
    {components : List (PathComponent ι α)}
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) :
    List.Perm (componentLabels (replaceComponents components left right k))
      (componentLabels components) := by
  have hright' : right ∈ components.erase left :=
    (List.mem_erase_of_ne hne.symm).2 hright
  have hcomponents :
      List.Perm components
        (left :: right :: (components.erase left).erase right) :=
    (List.perm_cons_erase hleft).trans
      ((List.perm_cons_erase hright').cons left)
  have hflat :
      List.Perm (componentLabels components)
        (componentLabels (left :: right ::
          (components.erase left).erase right)) := by
    exact hcomponents.flatMap
      (fun component _ => List.Perm.refl component.labels)
  simpa [componentLabels, replaceComponents, List.append_assoc] using hflat.symm

end Replacement

section Runs

variable {ι : Type u} {α : Type v} [DecidableEq ι] [DecidableEq α]

/-- One labelled greedy merge.  Its edge index is definitionally the
original last-to-first endpoint edge selected by the merge. -/
inductive LabelledGreedyStep (weight : ι → ι → Nat) :
    List (PathComponent ι α) → List (PathComponent ι α) → (ι × ι) → Prop where
  | merge {components : List (PathComponent ι α)}
      (left right : PathComponent ι α) (k : Nat)
      (left_mem : left ∈ components) (right_mem : right ∈ components)
      (distinct : left ≠ right)
      (overlap : IsOverlap left.text right.text k)
      (global : GloballyMaximal (componentWords components) k) :
      LabelledGreedyStep weight components
        (replaceComponents components left right k) (left.last, right.first)

/-- A labelled greedy run together with its selected original endpoint edges
in chronological order. -/
inductive LabelledGreedyRun (weight : ι → ι → Nat) :
    List (PathComponent ι α) → List (PathComponent ι α) →
      List (ι × ι) → Prop where
  | refl (components : List (PathComponent ι α)) :
      LabelledGreedyRun weight components components []
  | tail {start current next : List (PathComponent ι α)}
      {edges : List (ι × ι)} {edge : ι × ι}
      (run : LabelledGreedyRun weight start current edges)
      (step : LabelledGreedyStep weight current next edge) :
      LabelledGreedyRun weight start next (edges ++ [edge])

/-- Total original-table weight of the edges stored by a labelled run. -/
def selectedWeight (weight : ι → ι → Nat) (edges : List (ι × ι)) : Nat :=
  (edges.map fun edge => weight edge.1 edge.2).sum

/-- All one-step consequences needed by the run induction. -/
structure LabelledStepResult (weight : ι → ι → Nat)
    (before after : List (PathComponent ι α)) (edge : ι × ι) : Prop where
  literal_step : GreedyStep (componentWords before) (componentWords after)
  next_state : PathState weight after
  labels_perm : List.Perm (componentLabels after) (componentLabels before)
  rendered_length_add :
    renderedLength after + weight edge.1 edge.2 = renderedLength before

namespace LabelledGreedyStep

/-- Lift a legal component merge through `PathState.update`. -/
theorem lift
    {weight : ι → ι → Nat}
    {before after : List (PathComponent ι α)} {edge : ι × ι}
    (step : LabelledGreedyStep weight before after edge)
    (state : PathState weight before) :
    LabelledStepResult weight before after edge := by
  cases step with
  | merge left right k hleft hright hne hoverlap hglobal =>
      have update := state.update hleft hright hne hoverlap hglobal
      refine ⟨?_, update.next_state,
        componentLabels_replaceComponents hleft hright hne, ?_⟩
      · exact GreedyStep.mk left.text right.text k
          (PathState.mem_componentWords hleft)
          (PathState.mem_componentWords hright)
          (state.text_ne hleft hright hne) hoverlap hglobal update.words_eq
      · simpa using update.rendered_length_add

end LabelledGreedyStep

/-- Invariants accumulated along a labelled greedy run. -/
structure PathRunInvariant (weight : ι → ι → Nat)
    (start final : List (PathComponent ι α)) (edges : List (ι × ι)) : Prop where
  final_state : PathState weight final
  labels_perm : List.Perm (componentLabels final) (componentLabels start)
  rendered_length_add :
    renderedLength final + selectedWeight weight edges = renderedLength start
  literal_run : GreedyRun (componentWords start) (componentWords final)

namespace LabelledGreedyRun

/-- Path state, label partition, literal run, and length conservation are all
preserved by induction over a labelled greedy run. -/
theorem invariant
    {weight : ι → ι → Nat}
    {start final : List (PathComponent ι α)} {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight start final edges)
    (initialState : PathState weight start) :
    PathRunInvariant weight start final edges := by
  induction run with
  | refl =>
      exact ⟨initialState, .refl _, by simp [selectedWeight],
        GreedyRun.refl _⟩
  | tail run step ih =>
      have previous := ih
      have lifted := step.lift previous.final_state
      refine ⟨lifted.next_state,
        lifted.labels_perm.trans previous.labels_perm, ?_,
        GreedyRun.tail previous.literal_run lifted.literal_step⟩
      have hprevious := previous.rendered_length_add
      have hstep := lifted.rendered_length_add
      simp [selectedWeight, List.map_append, List.sum_append] at hprevious hstep ⊢
      omega

end LabelledGreedyRun

end Runs

section Terminal

variable {ι : Type u} {α : Type v} [DecidableEq ι] [DecidableEq α]

/-- A path is Hamiltonian for the supplied finite original-label list when it
is a permutation of that list. -/
def IsHamiltonianPermutation (labels path : List ι) : Prop :=
  path.Perm labels

/-- Terminal consequences of a labelled run from singleton components. -/
structure TerminalPathResult
    (original : ι → Word α) (weight : ι → ι → Nat)
    (labels : List ι) (terminal : PathComponent ι α)
    (edges : List (ι × ι)) : Prop where
  final_state : PathState weight [terminal]
  hamiltonian : IsHamiltonianPermutation labels terminal.labels
  labels_nodup : terminal.labels.Nodup
  rendered_length_add :
    terminal.text.length + selectedWeight weight edges =
      totalOriginalLength original labels
  rendered_length :
    terminal.text.length = totalOriginalLength original labels -
      selectedWeight weight edges
  literal_run :
    GreedyRun (labels.map original) [terminal.text]

namespace LabelledGreedyRun

/-- A singleton terminal component is a Hamiltonian path through the original
labels, and its literal length is the original total minus exactly the stored
last-to-first edge weights. -/
theorem terminalPath
    {original : ι → Word α} {weight : ι → ι → Nat}
    {labels : List ι} {terminal : PathComponent ι α}
    {edges : List (ι × ι)}
    (hlabels : labels.Nodup)
    (hreduced : Reduced (labels.map original))
    (htable : OriginalMaxOverlapTable original weight)
    (run : LabelledGreedyRun weight (initialComponents original labels)
      [terminal] edges) :
    TerminalPathResult original weight labels terminal edges := by
  have initialState := PathState.initial hreduced htable
  have invariant := run.invariant initialState
  have hperm : terminal.labels.Perm labels := by
    simpa only [componentLabels_singleton,
      componentLabels_initialComponents] using invariant.labels_perm
  have hterminalNodup : terminal.labels.Nodup :=
    hperm.nodup_iff.mpr hlabels
  have hlength :
      terminal.text.length + selectedWeight weight edges =
        totalOriginalLength original labels := by
    simpa only [renderedLength_singleton,
      renderedLength_initialComponents] using invariant.rendered_length_add
  have hsubtract :
      terminal.text.length = totalOriginalLength original labels -
        selectedWeight weight edges := by
    omega
  refine ⟨invariant.final_state, hperm, hterminalNodup,
    hlength, hsubtract, ?_⟩
  simpa only [componentWords_initialComponents,
    componentWords_singleton] using invariant.literal_run

end LabelledGreedyRun

end Terminal

end GreedySuperstring
