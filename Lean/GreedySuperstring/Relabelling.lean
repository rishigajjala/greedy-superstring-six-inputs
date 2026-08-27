import GreedySuperstring.OptimalBridge
import GreedySuperstring.PathRun

/-!
# Relabelling finite word instances

A Hamiltonian order determines an equivalence from canonical positions to
the old labels.  Reindexing along this equivalence preserves every semantic
word property while turning the nominated order into canonical order.
-/

namespace GreedySuperstring.Relaxation

namespace HamiltonianOrder

/-- The ordinary label list represented by a Hamiltonian order. -/
def labels (order : HamiltonianOrder n) : List (Fin n) :=
  order.head :: order.rest

@[simp] theorem labels_length (order : HamiltonianOrder n) :
    order.labels.length = n := by
  have hlength := order.perm.length_eq
  simpa [labels] using hlength

theorem labels_nodup (order : HamiltonianOrder n) :
    order.labels.Nodup := by
  exact order.nodup

/-- The old label occupying one canonical path position. -/
def positionLabel (order : HamiltonianOrder n) (position : Fin n) : Fin n :=
  order.labels.get (Fin.cast order.labels_length.symm position)

theorem positionLabel_injective (order : HamiltonianOrder n) :
    Function.Injective order.positionLabel := by
  intro i j hij
  apply Fin.cast_injective order.labels_length.symm
  exact order.labels_nodup.injective_get hij

theorem positionLabel_surjective (order : HamiltonianOrder n) :
    Function.Surjective order.positionLabel := by
  intro label
  have hcanonical : label ∈ List.ofFn id := by simp
  have hlabels : label ∈ order.labels := order.perm.mem_iff.mpr hcanonical
  obtain ⟨position, hposition⟩ := List.mem_iff_get.mp hlabels
  refine ⟨Fin.cast order.labels_length position, ?_⟩
  simpa [positionLabel] using hposition

/-- Equivalence from canonical path positions to the old labels in `order`. -/
noncomputable def labelEquiv (order : HamiltonianOrder n) : Fin n ≃ Fin n :=
  Equiv.ofBijective order.positionLabel
    ⟨order.positionLabel_injective,
      order.positionLabel_surjective⟩

@[simp] theorem labelEquiv_apply (order : HamiltonianOrder n)
    (position : Fin n) :
    order.labelEquiv position = order.positionLabel position := rfl

/-- Enumerating the position equivalence recovers the nominated order. -/
theorem ofFn_labelEquiv (order : HamiltonianOrder n) :
    List.ofFn order.labelEquiv = order.labels := by
  apply List.ext_get
  · simp
  · intro i hiLeft hiRight
    rw [List.get_ofFn, labelEquiv_apply]
    rfl

/-- Reindex a Hamiltonian order from old labels to new labels. -/
def reindex (order : HamiltonianOrder n) (equiv : Fin n ≃ Fin n) :
    HamiltonianOrder n where
  head := equiv.symm order.head
  rest := order.rest.map equiv.symm
  perm := by
    have hold := order.perm.map equiv.symm
    have hcanonical :=
      Equiv.Perm.ofFn_comp_perm equiv.symm (id : Fin n → Fin n)
    have hmapped :
        (equiv.symm order.head :: order.rest.map equiv.symm).Perm
          ((List.ofFn id).map equiv.symm) := by
      simpa using hold
    have hcanonical' :
        ((List.ofFn id).map equiv.symm).Perm (List.ofFn id) := by
      simpa [List.map_ofFn, Function.comp_def] using hcanonical
    exact hmapped.trans hcanonical'

/-- A Hamiltonian order is canonical when its labels occur in `Fin` order. -/
def IsCanonical (order : HamiltonianOrder n) : Prop :=
  order.labels = List.ofFn id

/-- Relabelling by the nominated order's position equivalence makes that
order canonical. -/
theorem reindex_labelEquiv_isCanonical (order : HamiltonianOrder n) :
    (order.reindex order.labelEquiv).IsCanonical := by
  unfold IsCanonical reindex labels
  change order.labels.map order.labelEquiv.symm = List.ofFn id
  calc
    order.labels.map order.labelEquiv.symm =
        (List.ofFn order.labelEquiv).map order.labelEquiv.symm := by
      rw [order.ofFn_labelEquiv]
    _ = List.ofFn (order.labelEquiv.symm ∘ order.labelEquiv) := by
      rw [List.map_ofFn]
    _ = List.ofFn id := by
      congr 1
      funext i
      exact order.labelEquiv.symm_apply_apply i

end HamiltonianOrder

namespace WordInstance

/-- Reindex all labelled data along an equivalence from new labels to old
labels.  Literal words and the common superstring are unchanged. -/
def reindex (data : WordInstance α n) (equiv : Fin n ≃ Fin n) :
    WordInstance α n where
  word i := data.word (equiv i)
  common := data.common
  overlap i j := data.overlap (equiv i) (equiv j)
  reduced := by
    have hperm := Equiv.Perm.ofFn_comp_perm equiv data.word
    constructor
    · exact hperm.nodup_iff.mpr data.reduced.1
    · intro left right hleft hright hne
      exact data.reduced.2 (hperm.mem_iff.mp hleft)
        (hperm.mem_iff.mp hright) hne
  maximum := by
    intro i j hne
    exact data.maximum (equiv i) (equiv j)
      (fun hij => hne (equiv.injective hij))
  occurrence i := data.occurrence (equiv i)

@[simp] theorem reindex_word (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) (i : Fin n) :
    (data.reindex equiv).word i = data.word (equiv i) := rfl

@[simp] theorem reindex_common (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) :
    (data.reindex equiv).common = data.common := rfl

@[simp] theorem reindex_overlap (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) (i j : Fin n) :
    (data.reindex equiv).overlap i j = data.overlap (equiv i) (equiv j) := rfl

@[simp] theorem reindex_occurrence (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) (i : Fin n) :
    (data.reindex equiv).occurrence i = data.occurrence (equiv i) := rfl

theorem reindex_reduced (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) :
    Reduced (List.ofFn (data.reindex equiv).word) :=
  (data.reindex equiv).reduced

theorem reindex_maximum (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) {i j : Fin n} (hne : i ≠ j) :
    IsMaxOverlap (data.word (equiv i)) (data.word (equiv j))
      (data.overlap (equiv i) (equiv j)) :=
  (data.reindex equiv).maximum i j hne

@[simp] theorem reindex_inputLength (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) (i : Fin n) :
    (data.reindex equiv).inputLength i = data.inputLength (equiv i) := rfl

@[simp] theorem reindex_optimumLength (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) :
    (data.reindex equiv).optimumLength = data.optimumLength := rfl

/-- Relabelling preserves the sum of all input lengths. -/
theorem reindex_totalInputLength (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) :
    (data.reindex equiv).totalInputLength = data.totalInputLength := by
  have hperm := Equiv.Perm.ofFn_comp_perm equiv data.inputLength
  have hsum := hperm.sum_eq
  simpa [WordInstance.totalInputLength, Function.comp_def] using hsum

/-- Shortest-common-superstring minimality is invariant under relabelling. -/
theorem reindex_shortest_iff (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) :
    IsShortestCommonSuperstring (data.reindex equiv) ↔
      IsShortestCommonSuperstring data := by
  constructor
  · intro shortest candidate contains
    apply shortest candidate
    intro i
    simpa using contains (equiv i)
  · intro shortest candidate contains
    apply shortest candidate
    intro i
    simpa using contains (equiv.symm i)

private theorem pathWeight_reindex (data : WordInstance α n)
    (equiv : Fin n ≃ Fin n) (head : Fin n) (rest : List (Fin n)) :
    pathWeight (data.reindex equiv).overlap (equiv.symm head)
        (rest.map equiv.symm) =
      pathWeight data.overlap head rest := by
  induction rest generalizing head with
  | nil => rfl
  | cons next remaining ih =>
      simp [pathWeight, ih]

/-- Reindexing both the data and a Hamiltonian order preserves its complete
directed overlap saving. -/
theorem reindex_overlapWeight (data : WordInstance α n)
    (order : HamiltonianOrder n) (equiv : Fin n ≃ Fin n) :
    (order.reindex equiv).overlapWeight (data.reindex equiv) =
      order.overlapWeight data := by
  exact pathWeight_reindex data equiv order.head order.rest

/-- Reindexing both data and order preserves the literal path length. -/
theorem reindex_path_superstring_length (data : WordInstance α n)
    (order : HamiltonianOrder n) (equiv : Fin n ≃ Fin n) :
    ((order.reindex equiv).toOverlapPath (data.reindex equiv)).superstring.length =
      (order.toOverlapPath data).superstring.length := by
  have newAdd :=
    ((order.reindex equiv).toOverlapPath
      (data.reindex equiv)).length_add_overlapSum
  have oldAdd := (order.toOverlapPath data).length_add_overlapSum
  have newTotal :=
    (order.reindex equiv).totalWordLength_eq_totalInputLength
      (data.reindex equiv)
  have oldTotal := order.totalWordLength_eq_totalInputLength data
  have newOverlap :=
    (order.reindex equiv).toOverlapPath_overlapSum (data.reindex equiv)
  have oldOverlap := order.toOverlapPath_overlapSum data
  rw [newTotal, newOverlap, reindex_totalInputLength,
    reindex_overlapWeight] at newAdd
  rw [oldTotal, oldOverlap] at oldAdd
  omega

/-- Exact optimum-path length is invariant under simultaneous relabelling. -/
theorem reindex_path_exact_iff (data : WordInstance α n)
    (order : HamiltonianOrder n) (equiv : Fin n ≃ Fin n) :
    ((order.reindex equiv).toOverlapPath
        (data.reindex equiv)).superstring.length =
        (data.reindex equiv).optimumLength ↔
      (order.toOverlapPath data).superstring.length = data.optimumLength := by
  rw [reindex_path_superstring_length, reindex_optimumLength]

end WordInstance

end GreedySuperstring.Relaxation

namespace GreedySuperstring

namespace LabelPath

/-- Relabel every vertex of a nonempty label path. -/
def relabel (equiv : ι ≃ κ) (path : LabelPath ι) : LabelPath κ where
  first := equiv path.first
  rest := path.rest.map equiv

@[simp] theorem labels_relabel (equiv : ι ≃ κ) (path : LabelPath ι) :
    (path.relabel equiv).labels = path.labels.map equiv := by
  simp [relabel, labels]

@[simp] theorem first_relabel (equiv : ι ≃ κ) (path : LabelPath ι) :
    (path.relabel equiv).first = equiv path.first := rfl

@[simp] theorem relabel_symm_relabel (equiv : ι ≃ κ)
    (path : LabelPath ι) :
    (path.relabel equiv).relabel equiv.symm = path := by
  cases path
  simp [relabel]

theorem relabel_injective (equiv : ι ≃ κ) :
    Function.Injective (relabel equiv : LabelPath ι → LabelPath κ) := by
  intro left right heq
  have := congrArg (relabel equiv.symm) heq
  simpa using this

@[simp] theorem relabel_append (equiv : ι ≃ κ)
    (left right : LabelPath ι) :
    (left.append right).relabel equiv =
      (left.relabel equiv).append (right.relabel equiv) := by
  cases left
  cases right
  simp [relabel, append, List.map_append]

/-- Relabelling preserves the terminal label of a nonempty path.  The proof
uses only the public singleton and append equations for `last`. -/
@[simp] theorem last_relabel (equiv : ι ≃ κ) (path : LabelPath ι) :
    (path.relabel equiv).last = equiv path.last := by
  rcases path with ⟨first, rest⟩
  induction rest generalizing first with
  | nil =>
      have hleft := PathComponent.last_singleton (α := Unit)
        (fun _ : κ => ([] : Word Unit)) (equiv first)
      have hright := PathComponent.last_singleton (α := Unit)
        (fun _ : ι => ([] : Word Unit)) first
      simpa [relabel, PathComponent.singleton, PathComponent.last] using
        hleft.trans (congrArg equiv hright.symm)
  | cons next remaining ih =>
      rw [show
        (LabelPath.mk first (next :: remaining)).relabel equiv =
          (LabelPath.mk (equiv first) []).append
            ((LabelPath.mk next remaining).relabel equiv) by rfl]
      rw [LabelPath.last_append]
      rw [show LabelPath.mk first (next :: remaining) =
        (LabelPath.mk first []).append (LabelPath.mk next remaining) by rfl]
      rw [LabelPath.last_append]
      exact ih next

end LabelPath

namespace PathComponent

/-- Relabel a component's path while leaving its literal text unchanged. -/
def relabel (equiv : ι ≃ κ) (component : PathComponent ι α) :
    PathComponent κ α where
  path := component.path.relabel equiv
  text := component.text

@[simp] theorem labels_relabel (equiv : ι ≃ κ)
    (component : PathComponent ι α) :
    (component.relabel equiv).labels = component.labels.map equiv := by
  simp [relabel, labels]

@[simp] theorem first_relabel (equiv : ι ≃ κ)
    (component : PathComponent ι α) :
    (component.relabel equiv).first = equiv component.first := rfl

@[simp] theorem text_relabel (equiv : ι ≃ κ)
    (component : PathComponent ι α) :
    (component.relabel equiv).text = component.text := rfl

@[simp] theorem last_relabel (equiv : ι ≃ κ)
    (component : PathComponent ι α) :
    (component.relabel equiv).last = equiv component.last :=
  LabelPath.last_relabel equiv component.path

@[simp] theorem relabel_symm_relabel (equiv : ι ≃ κ)
    (component : PathComponent ι α) :
    (component.relabel equiv).relabel equiv.symm = component := by
  cases component
  simp [relabel]

theorem relabel_injective (equiv : ι ≃ κ) :
    Function.Injective
      (relabel equiv : PathComponent ι α → PathComponent κ α) := by
  intro left right heq
  have := congrArg (relabel equiv.symm) heq
  simpa using this

@[simp] theorem relabel_merge (equiv : ι ≃ κ)
    (left right : PathComponent ι α) (k : Nat) :
    (left.merge right k).relabel equiv =
      (left.relabel equiv).merge (right.relabel equiv) k := by
  cases left
  cases right
  simp [relabel, merge]

end PathComponent

/-- Relabel both endpoints of an edge. -/
def relabelEdge (equiv : ι ≃ κ) (edge : ι × ι) : κ × κ :=
  (equiv edge.1, equiv edge.2)

/-- Pull an old weight table through a new-to-old label equivalence. -/
def reindexWeight (weight : ι → ι → Nat) (equiv : ι ≃ κ) :
    κ → κ → Nat :=
  fun i j => weight (equiv.symm i) (equiv.symm j)

@[simp] theorem componentWords_map_relabel (equiv : ι ≃ κ)
    (components : List (PathComponent ι α)) :
    componentWords (components.map (PathComponent.relabel equiv)) =
      componentWords components := by
  simp [componentWords]

@[simp] theorem map_relabel_initialComponents (equiv : ι ≃ κ)
    (original : ι → Word α) (labels : List ι) :
    (initialComponents original labels).map (PathComponent.relabel equiv) =
      initialComponents (fun label => original (equiv.symm label))
        (labels.map equiv) := by
  simp [initialComponents, PathComponent.singleton,
    PathComponent.relabel, LabelPath.relabel, List.map_map,
    Function.comp_def]

/-- Selected-edge weight is unchanged when the table and stored edges are
transported together. -/
theorem selectedWeight_relabel (weight : ι → ι → Nat) (equiv : ι ≃ κ)
    (edges : List (ι × ι)) :
    selectedWeight (reindexWeight weight equiv)
        (edges.map (relabelEdge equiv)) =
      selectedWeight weight edges := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      simp only [selectedWeight, List.map_cons, List.sum_cons] at ih ⊢
      rw [List.map_map] at ih
      simpa [reindexWeight, relabelEdge, Function.comp_def] using
        congrArg (weight edge.1 edge.2 + ·) ih

section ComponentReplacement

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

/-- Component replacement commutes with injective relabelling. -/
theorem map_relabel_replaceComponents (equiv : ι ≃ κ)
    (components : List (PathComponent ι α))
    (left right : PathComponent ι α) (k : Nat) :
    (replaceComponents components left right k).map
        (PathComponent.relabel equiv) =
      replaceComponents
        (components.map (PathComponent.relabel equiv))
        (left.relabel equiv) (right.relabel equiv) k := by
  simp [replaceComponents, PathComponent.relabel_merge,
    List.map_erase (PathComponent.relabel_injective equiv)]

end ComponentReplacement

section RunTransport

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

namespace LabelledGreedyStep

/-- A labelled greedy step can be replayed after permuting the component
forest.  The chosen components, literal merge, endpoint edge, and overlap
certificate are unchanged; only the list order of the untouched components
may differ. -/
theorem replay_of_perm
    {weight : ι → ι → Nat}
    {before after before' : List (PathComponent ι α)} {edge : ι × ι}
    (step : LabelledGreedyStep weight before after edge)
    (hperm : before'.Perm before) :
    ∃ after', LabelledGreedyStep weight before' after' edge ∧
      after'.Perm after := by
  cases step with
  | merge left right k hleft hright hne hoverlap hglobal =>
      have hleft' : left ∈ before' := hperm.mem_iff.mpr hleft
      have hright' : right ∈ before' := hperm.mem_iff.mpr hright
      have wordPerm : (componentWords before').Perm (componentWords before) := by
        simpa [componentWords] using hperm.map PathComponent.text
      have hglobal' : GloballyMaximal (componentWords before') k := by
        intro x y hx hy hxy
        exact hglobal (wordPerm.mem_iff.mp hx) (wordPerm.mem_iff.mp hy) hxy
      refine ⟨replaceComponents before' left right k,
        LabelledGreedyStep.merge left right k hleft' hright' hne
          hoverlap hglobal', ?_⟩
      have erasedLeft : (before'.erase left).Perm (before.erase left) :=
        hperm.erase left
      have erasedRight :
          ((before'.erase left).erase right).Perm
            ((before.erase left).erase right) :=
        erasedLeft.erase right
      exact erasedRight.cons (left.merge right k)

/-- A labelled greedy step transports across a label equivalence. -/
theorem relabel
    {weight : ι → ι → Nat}
    {before after : List (PathComponent ι α)} {edge : ι × ι}
    (step : LabelledGreedyStep weight before after edge)
    (equiv : ι ≃ κ) :
    LabelledGreedyStep (reindexWeight weight equiv)
      (before.map (PathComponent.relabel equiv))
      (after.map (PathComponent.relabel equiv))
      (relabelEdge equiv edge) := by
  cases step with
  | merge left right k hleft hright hne hoverlap hglobal =>
      have hleft' : left.relabel equiv ∈
          before.map (PathComponent.relabel equiv) :=
        List.mem_map_of_mem (f := PathComponent.relabel equiv) hleft
      have hright' : right.relabel equiv ∈
          before.map (PathComponent.relabel equiv) :=
        List.mem_map_of_mem (f := PathComponent.relabel equiv) hright
      have hne' : left.relabel equiv ≠ right.relabel equiv :=
        (PathComponent.relabel_injective equiv).ne hne
      have hglobal' :
          GloballyMaximal
            (componentWords
              (before.map (PathComponent.relabel equiv))) k := by
        simpa using hglobal
      have transported := LabelledGreedyStep.merge
        (weight := reindexWeight weight equiv)
        (left.relabel equiv) (right.relabel equiv) k
        hleft' hright' hne' hoverlap hglobal'
      rw [map_relabel_replaceComponents equiv before left right k]
      simpa [relabelEdge] using transported

end LabelledGreedyStep

namespace LabelledGreedyRun

/-- Replay a complete run from a permutation of its starting component
forest.  Every selected endpoint edge is retained in the same chronological
position, and the resulting final forest is a permutation of the original
one. -/
theorem replay_of_perm
    {weight : ι → ι → Nat}
    {start final start' : List (PathComponent ι α)}
    {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight start final edges)
    (hperm : start'.Perm start) :
    ∃ final', LabelledGreedyRun weight start' final' edges ∧
      final'.Perm final := by
  induction run generalizing start' with
  | refl =>
      exact ⟨start', LabelledGreedyRun.refl start', hperm⟩
  | tail run step ih =>
      obtain ⟨current', run', hcurrent⟩ := ih hperm
      obtain ⟨next', step', hnext⟩ := step.replay_of_perm hcurrent
      exact ⟨next', LabelledGreedyRun.tail run' step', hnext⟩

/-- When the original run has a singleton terminal forest, replaying it from
a permuted start has that very same terminal forest, rather than merely a
permutation of it. -/
theorem replay_singleton_of_perm
    {weight : ι → ι → Nat}
    {start start' : List (PathComponent ι α)}
    {terminal : PathComponent ι α} {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight start [terminal] edges)
    (hperm : start'.Perm start) :
    LabelledGreedyRun weight start' [terminal] edges := by
  obtain ⟨final', replayed, hfinal⟩ := run.replay_of_perm hperm
  have hsingleton : final' = [terminal] := by
    simpa using hfinal
  subst final'
  exact replayed

/-- Every labelled greedy run, including its chronological edge list,
transports across a label equivalence. -/
theorem relabel
    {weight : ι → ι → Nat}
    {start final : List (PathComponent ι α)} {edges : List (ι × ι)}
    (run : LabelledGreedyRun weight start final edges)
    (equiv : ι ≃ κ) :
    LabelledGreedyRun (reindexWeight weight equiv)
      (start.map (PathComponent.relabel equiv))
      (final.map (PathComponent.relabel equiv))
      (edges.map (relabelEdge equiv)) := by
  induction run with
  | refl =>
      exact LabelledGreedyRun.refl _
  | tail run step ih =>
      have transportedStep := step.relabel equiv
      simpa [List.map_append] using
        LabelledGreedyRun.tail ih transportedStep

end LabelledGreedyRun

end RunTransport

open Relaxation

/-- Complete output of relabelling a terminal run by its terminal label
order.  The `run` field exposes the reindexed word instance, transported
component forest, terminal component, and chronological edge list. -/
structure CanonicalRunRelabelling
    [DecidableEq α]
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n)) where
  order : HamiltonianOrder n
  order_labels : order.labels = terminal.labels
  run :
    LabelledGreedyRun (data.reindex order.labelEquiv).overlap
      ((initialComponents data.word (List.ofFn id)).map
        (PathComponent.relabel order.labelEquiv.symm))
      [terminal.relabel order.labelEquiv.symm]
      (edges.map (relabelEdge order.labelEquiv.symm))
  start_perm :
    List.Perm
      ((initialComponents data.word (List.ofFn id)).map
        (PathComponent.relabel order.labelEquiv.symm))
      (initialComponents (data.reindex order.labelEquiv).word
        (List.ofFn id))
  terminal_labels_canonical :
    (terminal.relabel order.labelEquiv.symm).labels = List.ofFn id
  terminal_text_preserved :
    (terminal.relabel order.labelEquiv.symm).text = terminal.text
  selectedWeight_preserved :
    selectedWeight (data.reindex order.labelEquiv).overlap
        (edges.map (relabelEdge order.labelEquiv.symm)) =
      selectedWeight data.overlap edges

namespace CanonicalRunRelabelling

variable {α : Type u} {n : Nat} [DecidableEq α]
  {data : WordInstance α n} {terminal : PathComponent (Fin n) α}
  {edges : List (Fin n × Fin n)}

/-- The reindexed semantic word instance exposed by the package. -/
noncomputable def reindexedData
    (result : CanonicalRunRelabelling data terminal edges) :
    WordInstance α n :=
  data.reindex result.order.labelEquiv

/-- The terminal component with canonical labels. -/
noncomputable def reindexedTerminal
    (result : CanonicalRunRelabelling data terminal edges) :
    PathComponent (Fin n) α :=
  terminal.relabel result.order.labelEquiv.symm

/-- The relabelled chronological edge sequence. -/
noncomputable def chronology
    (result : CanonicalRunRelabelling data terminal edges) :
    List (Fin n × Fin n) :=
  edges.map (relabelEdge result.order.labelEquiv.symm)

/-- The transported run replayed from the exact canonical singleton forest.
This is the form consumed by chronology alignment and dense LP bridges. -/
theorem canonicalRun
    (result : CanonicalRunRelabelling data terminal edges) :
    LabelledGreedyRun result.reindexedData.overlap
      (initialComponents result.reindexedData.word (List.ofFn id))
      [result.reindexedTerminal] result.chronology := by
  unfold reindexedData reindexedTerminal chronology
  exact result.run.replay_singleton_of_perm result.start_perm.symm

end CanonicalRunRelabelling

namespace LabelledGreedyRun

/-- Relabel a terminal run by the Hamiltonian order carried by its terminal
component.  The new terminal path is canonical and its literal text is
definitionally unchanged. -/
noncomputable def canonicalRelabelling
    [DecidableEq α]
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n))
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges) :
    CanonicalRunRelabelling data terminal edges := by
  have hlabels : (List.ofFn (id : Fin n → Fin n)).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hreduced :
      Reduced ((List.ofFn (id : Fin n → Fin n)).map data.word) := by
    simpa [List.map_ofFn, Function.comp_def] using data.reduced
  have terminalResult := run.terminalPath hlabels hreduced data.maximum
  let order : HamiltonianOrder n :=
    { head := terminal.first
      rest := terminal.path.rest
      perm := by
        simpa [IsHamiltonianPermutation, PathComponent.labels,
          PathComponent.first, LabelPath.labels] using
          terminalResult.hamiltonian }
  have orderLabels : order.labels = terminal.labels := by
    rfl
  have weightEq :
      reindexWeight data.overlap order.labelEquiv.symm =
        (data.reindex order.labelEquiv).overlap := by
    funext i j
    simp [reindexWeight, WordInstance.reindex]
  have transported := run.relabel order.labelEquiv.symm
  have transported' :
      LabelledGreedyRun (data.reindex order.labelEquiv).overlap
        ((initialComponents data.word (List.ofFn id)).map
          (PathComponent.relabel order.labelEquiv.symm))
        [terminal.relabel order.labelEquiv.symm]
        (edges.map (relabelEdge order.labelEquiv.symm)) := by
    rw [← weightEq]
    exact transported
  have canonicalOrderLabels :
      order.labels.map order.labelEquiv.symm = List.ofFn id := by
    have hcanonical := order.reindex_labelEquiv_isCanonical
    simpa [HamiltonianOrder.IsCanonical, HamiltonianOrder.reindex,
      HamiltonianOrder.labels] using hcanonical
  have terminalCanonical :
      (terminal.relabel order.labelEquiv.symm).labels = List.ofFn id := by
    calc
      (terminal.relabel order.labelEquiv.symm).labels =
          terminal.labels.map order.labelEquiv.symm := by simp
      _ = order.labels.map order.labelEquiv.symm := by rw [orderLabels]
      _ = List.ofFn id := canonicalOrderLabels
  have startPerm :
      List.Perm
        ((initialComponents data.word (List.ofFn id)).map
          (PathComponent.relabel order.labelEquiv.symm))
        (initialComponents (data.reindex order.labelEquiv).word
          (List.ofFn id)) := by
    have labelPerm := Equiv.Perm.ofFn_comp_perm
      order.labelEquiv.symm (id : Fin n → Fin n)
    have labelPerm' :
        ((List.ofFn id).map order.labelEquiv.symm).Perm
          (List.ofFn id) := by
      simpa [List.map_ofFn, Function.comp_def] using labelPerm
    have componentPerm := labelPerm'.map
      (PathComponent.singleton (data.reindex order.labelEquiv).word)
    have positionSymm (label : Fin n) :
        order.positionLabel (order.labelEquiv.symm label) = label := by
      rw [← order.labelEquiv_apply]
      exact order.labelEquiv.apply_symm_apply label
    simpa [map_relabel_initialComponents, WordInstance.reindex,
      initialComponents, PathComponent.relabel, PathComponent.singleton,
      LabelPath.relabel, List.map_ofFn, Function.comp_def,
      positionSymm] using
        componentPerm
  have selectedPreserved :
      selectedWeight (data.reindex order.labelEquiv).overlap
          (edges.map (relabelEdge order.labelEquiv.symm)) =
        selectedWeight data.overlap edges := by
    rw [← weightEq]
    exact selectedWeight_relabel data.overlap order.labelEquiv.symm edges
  exact
    { order := order
      order_labels := orderLabels
      run := transported'
      start_perm := startPerm
      terminal_labels_canonical := terminalCanonical
      terminal_text_preserved := rfl
      selectedWeight_preserved := selectedPreserved }

/-- Proposition-level exported form of `canonicalRelabelling`. -/
theorem exists_canonicalRelabelling
    [DecidableEq α]
    (data : WordInstance α n) (terminal : PathComponent (Fin n) α)
    (edges : List (Fin n × Fin n))
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges) :
    ∃ result : CanonicalRunRelabelling data terminal edges,
      result.reindexedTerminal.text = terminal.text ∧
      result.reindexedTerminal.labels = List.ofFn id := by
  let result := run.canonicalRelabelling data terminal edges
  exact ⟨result, result.terminal_text_preserved,
    result.terminal_labels_canonical⟩

end LabelledGreedyRun

end GreedySuperstring
