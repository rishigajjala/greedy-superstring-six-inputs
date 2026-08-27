import GreedySuperstring.GreedyRun

/-!
# Original-label path states

This module records the path-forest invariant behind a literal greedy run.
Every current word carries a nonempty ordered path of original labels.  The
maximum overlap between two distinct current components is indexed by the
last label of the first path and the first label of the second path.
-/

namespace GreedySuperstring

section LabelPaths

variable {ι : Type u}

/-- A nonempty ordered list, represented by its first element and remaining
elements. -/
structure LabelPath (ι : Type u) where
  first : ι
  rest : List ι
  deriving DecidableEq

namespace LabelPath

/-- The ordinary list of labels carried by a nonempty label path. -/
def labels (path : LabelPath ι) : List ι :=
  path.first :: path.rest

private def lastAux (current : ι) : List ι → ι
  | [] => current
  | next :: rest => lastAux next rest

/-- The last label of a nonempty label path. -/
def last (path : LabelPath ι) : ι :=
  lastAux path.first path.rest

/-- Concatenate two nonempty label paths. -/
def append (left right : LabelPath ι) : LabelPath ι where
  first := left.first
  rest := left.rest ++ right.first :: right.rest

private theorem lastAux_append_cons (current next : ι) (xs ys : List ι) :
    lastAux current (xs ++ next :: ys) = lastAux next ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih => simpa [lastAux] using ih x

@[simp] theorem labels_ne_nil (path : LabelPath ι) : path.labels ≠ [] := by
  simp [labels]

@[simp] theorem labels_append (left right : LabelPath ι) :
    (left.append right).labels = left.labels ++ right.labels := by
  simp [append, labels]

@[simp] theorem first_append (left right : LabelPath ι) :
    (left.append right).first = left.first := rfl

@[simp] theorem last_append (left right : LabelPath ι) :
    (left.append right).last = right.last := by
  exact lastAux_append_cons left.first right.first left.rest right.rest

end LabelPath

end LabelPaths

section Components

variable {ι : Type u} {α : Type v}

/-- A literal current word together with the nonempty path of original labels
that has been merged into it. -/
structure PathComponent (ι : Type u) (α : Type v) where
  path : LabelPath ι
  text : Word α
  deriving DecidableEq

namespace PathComponent

def labels (component : PathComponent ι α) : List ι :=
  component.path.labels

def first (component : PathComponent ι α) : ι :=
  component.path.first

def last (component : PathComponent ι α) : ι :=
  component.path.last

/-- Merge the literal texts and concatenate their original-label paths. -/
def merge (left right : PathComponent ι α) (k : Nat) :
    PathComponent ι α where
  path := left.path.append right.path
  text := mergeAt left.text right.text k

@[simp] theorem labels_merge (left right : PathComponent ι α) (k : Nat) :
    (left.merge right k).labels = left.labels ++ right.labels := by
  simp [merge, labels]

@[simp] theorem first_merge (left right : PathComponent ι α) (k : Nat) :
    (left.merge right k).first = left.first := rfl

@[simp] theorem last_merge (left right : PathComponent ι α) (k : Nat) :
    (left.merge right k).last = right.last := by
  simp [merge, last]

@[simp] theorem text_merge (left right : PathComponent ι α) (k : Nat) :
    (left.merge right k).text = mergeAt left.text right.text k := rfl

end PathComponent

/-- A certified table of maximum overlaps between distinct original labels. -/
def OriginalMaxOverlapTable (original : ι → Word α)
    (weight : ι → ι → Nat) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → IsMaxOverlap (original i) (original j) (weight i j)

/-- Literal words underlying a list of labelled components. -/
def componentWords (components : List (PathComponent ι α)) :
    List (Word α) :=
  components.map PathComponent.text

/-- Sum of the lengths of all current literal component texts. -/
def renderedLength (components : List (PathComponent ι α)) : Nat :=
  (components.map fun component => component.text.length).sum

private theorem nodup_of_map_nodup
    {β : Type u} {γ : Type v} (f : β → γ) {items : List β}
    (hnodup : (items.map f).Nodup) : items.Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      have hcons := List.nodup_cons.mp hnodup
      rw [List.nodup_cons]
      exact ⟨fun hmem => hcons.1 (List.mem_map_of_mem (f := f) hmem),
        ih hcons.2⟩

private theorem nodup_append_of_disjoint
    {β : Type u} {left right : List β}
    (hleft : left.Nodup) (hright : right.Nodup)
    (hdisjoint : left.Disjoint right) : (left ++ right).Nodup := by
  induction left with
  | nil => simpa using hright
  | cons head tail ih =>
      have hcons := List.nodup_cons.mp hleft
      change (head :: (tail ++ right)).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_append.mp hmem with htail | hrightMem
        · exact hcons.1 htail
        · exact hdisjoint (by simp) hrightMem
      · apply ih hcons.2
        intro item htail hrightMem
        exact hdisjoint (by simp [htail]) hrightMem

private theorem eq_of_nodup_map_of_mem
    {β : Type u} {γ : Type v} (f : β → γ) {items : List β} {x y : β}
    (hnodup : (items.map f).Nodup)
    (hx : x ∈ items) (hy : y ∈ items) (hxy : f x = f y) : x = y := by
  induction items with
  | nil => simp at hx
  | cons head tail ih =>
      have hcons := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hx with hxh | hxTail
      · subst x
        rcases List.mem_cons.mp hy with hyh | hyTail
        · exact hyh.symm
        · exfalso
          apply hcons.1
          rw [hxy]
          exact List.mem_map_of_mem (f := f) hyTail
      · rcases List.mem_cons.mp hy with hyh | hyTail
        · subst y
          exfalso
          apply hcons.1
          rw [← hxy]
          exact List.mem_map_of_mem (f := f) hxTail
        · exact ih hcons.2 hxTail hyTail

section Decidable

variable [DecidableEq ι] [DecidableEq α]

/-- Replace two components by their merged component. -/
def replaceComponents (components : List (PathComponent ι α))
    (left right : PathComponent ι α) (k : Nat) :
    List (PathComponent ι α) :=
  left.merge right k :: (components.erase left).erase right

/-- Abstract membership description of a component-list replacement. -/
def AfterComponentMerge (components : List (PathComponent ι α))
    (left right : PathComponent ι α) (k : Nat)
    (component : PathComponent ι α) : Prop :=
  component = left.merge right k ∨
    (component ∈ components ∧ component ≠ left ∧ component ≠ right)

theorem mem_replaceComponents_iff_after
    {components : List (PathComponent ι α)}
    {left right component : PathComponent ι α} {k : Nat}
    (hnodup : components.Nodup) :
    component ∈ replaceComponents components left right k ↔
      AfterComponentMerge components left right k component := by
  simp only [replaceComponents, List.mem_cons, AfterComponentMerge]
  constructor
  · rintro (hmerge | htail)
    · exact Or.inl hmerge
    · have hright := (hnodup.erase left).mem_erase_iff.mp htail
      have hleft := hnodup.mem_erase_iff.mp hright.2
      exact Or.inr ⟨hleft.2, hleft.1, hright.1⟩
  · rintro (hmerge | ⟨hmem, hleft, hright⟩)
    · exact Or.inl hmerge
    · exact Or.inr <| (hnodup.erase left).mem_erase_iff.mpr
        ⟨hright, hnodup.mem_erase_iff.mpr ⟨hleft, hmem⟩⟩

private theorem map_erase_of_map_nodup
    {β : Type u} {γ : Type v}
    [BEq β] [LawfulBEq β] [BEq γ] [LawfulBEq γ]
    (f : β → γ) {items : List β} {item : β}
    (hnodup : (items.map f).Nodup) (hmem : item ∈ items) :
    (items.erase item).map f = (items.map f).erase (f item) := by
  induction items with
  | nil => simp at hmem
  | cons head tail ih =>
      have hcons := List.nodup_cons.mp hnodup
      by_cases heq : head = item
      · subst head
        simp
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact (heq hhead.symm).elim
          · exact htail
        have hfne : f head ≠ f item := by
          intro hfeq
          apply hcons.1
          rw [hfeq]
          exact List.mem_map_of_mem (f := f) htail
        simp [heq, hfne, ih hcons.2 htail]

/-- Component replacement and literal-word replacement agree exactly when
the current literal texts are duplicate-free. -/
theorem componentWords_replaceComponents
    {components : List (PathComponent ι α)}
    {left right : PathComponent ι α} {k : Nat}
    (hnodup : (componentWords components).Nodup)
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) :
    componentWords (replaceComponents components left right k) =
      replaceMerge (componentWords components) left.text right.text k := by
  have hright' : right ∈ components.erase left :=
    (List.mem_erase_of_ne hne.symm).2 hright
  have heraseLeft := map_erase_of_map_nodup
    (f := PathComponent.text) hnodup hleft
  have hafterLeft :
      ((components.erase left).map PathComponent.text).Nodup := by
    rw [heraseLeft]
    exact hnodup.erase left.text
  have heraseRight := map_erase_of_map_nodup
    (f := PathComponent.text) hafterLeft hright'
  simp only [componentWords, replaceComponents, replaceMerge, List.map_cons,
    PathComponent.text_merge]
  rw [heraseRight, heraseLeft]

private theorem sum_map_erase_add
    {β : Type u} [BEq β] [LawfulBEq β] (value : β → Nat)
    {items : List β} {item : β} (hmem : item ∈ items) :
    ((items.erase item).map value).sum + value item =
      (items.map value).sum := by
  induction items with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases heq : head = item
      · subst head
        simp [Nat.add_comm]
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact (heq hhead.symm).elim
          · exact htail
        have hih := ih htail
        simp [heq] at hih ⊢
        omega

/-- A literal component merge lowers the total current text length by exactly
the chosen overlap.  The additive form avoids truncated subtraction. -/
theorem renderedLength_replaceComponents_add
    {components : List (PathComponent ι α)}
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k) :
    renderedLength (replaceComponents components left right k) + k =
      renderedLength components := by
  have hright' : right ∈ components.erase left :=
    (List.mem_erase_of_ne hne.symm).2 hright
  have hsumLeft := sum_map_erase_add
    (fun component : PathComponent ι α => component.text.length) hleft
  have hsumRight := sum_map_erase_add
    (fun component : PathComponent ι α => component.text.length) hright'
  have hmergeLength :
      (mergeAt left.text right.text k).length =
        left.text.length + right.text.length - k :=
    mergeAt_length hoverlap.2.1
  have hk : k ≤ right.text.length := hoverlap.2.1
  simp only [renderedLength, replaceComponents, List.map_cons, List.sum_cons,
    PathComponent.text_merge] at hsumLeft hsumRight hmergeLength ⊢
  omega

end Decidable

end Components

section State

variable {ι : Type u} {α : Type v}

/-- The original-label path-forest invariant for a current component list. -/
structure PathState (weight : ι → ι → Nat)
    (components : List (PathComponent ι α)) : Prop where
  reduced : Reduced (componentWords components)
  labels_nodup : ∀ ⦃component⦄, component ∈ components → component.labels.Nodup
  labels_disjoint : ∀ ⦃left⦄, left ∈ components →
    ∀ ⦃right⦄, right ∈ components → left ≠ right →
      left.labels.Disjoint right.labels
  interface : ∀ ⦃left⦄, left ∈ components →
    ∀ ⦃right⦄, right ∈ components → left ≠ right →
      IsMaxOverlap left.text right.text (weight left.last right.first)

namespace PathState

theorem mem_componentWords {components : List (PathComponent ι α)}
    {component : PathComponent ι α} (hmem : component ∈ components) :
    component.text ∈ componentWords components := by
  exact List.mem_map_of_mem (f := PathComponent.text) hmem

theorem components_nodup {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components) : components.Nodup := by
  exact nodup_of_map_nodup PathComponent.text state.reduced.1

theorem text_ne {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) : left.text ≠ right.text := by
  intro htext
  exact hne (eq_of_nodup_map_of_mem PathComponent.text state.reduced.1
    hleft hright htext)

/-- The chosen current overlap is the original-table overlap from the left
component's last label to the right component's first label. -/
theorem selectedOverlap_eq
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    k = weight left.last right.first := by
  have htextNe := state.text_ne hleft hright hne
  have hselected : IsMaxOverlap left.text right.text k :=
    ⟨hoverlap, hglobal (mem_componentWords hleft)
      (mem_componentWords hright) htextNe⟩
  exact maxOverlap_unique hselected (state.interface hleft hright hne)

/-- Every outgoing overlap of the merge is inherited from the right
component. -/
theorem merged_outgoing_overlap_iff
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right external : PathComponent ι α} {k r : Nat}
    (hleft : left ∈ components) (hexternal : external ∈ components)
    (hne : left ≠ external) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    IsOverlap (left.merge right k).text external.text r ↔
      IsOverlap right.text external.text r := by
  exact right_overlap_interface_of_global hoverlap hglobal
    (mem_componentWords hleft) (mem_componentWords hexternal)
    (state.text_ne hleft hexternal hne)

/-- Every incoming overlap of the merge is inherited from the left
component. -/
theorem merged_incoming_overlap_iff
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {external left right : PathComponent ι α} {k r : Nat}
    (hexternal : external ∈ components) (hright : right ∈ components)
    (hne : external ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    IsOverlap external.text (left.merge right k).text r ↔
      IsOverlap external.text left.text r := by
  exact left_overlap_interface_of_global hoverlap hglobal
    (mem_componentWords hexternal) (mem_componentWords hright)
    (state.text_ne hexternal hright hne)

theorem merged_outgoing_interface
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right external : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hexternal : external ∈ components)
    (hle : left ≠ external) (hre : right ≠ external)
    (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    IsMaxOverlap (left.merge right k).text external.text
      (weight (left.merge right k).last external.first) := by
  have hbound := hglobal (mem_componentWords hleft)
    (mem_componentWords hexternal) (state.text_ne hleft hexternal hle)
  simpa using (right_maxOverlap_interface hoverlap hbound).mpr
    (state.interface hright hexternal hre)

theorem merged_incoming_interface
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {external left right : PathComponent ι α} {k : Nat}
    (hexternal : external ∈ components)
    (hleft : left ∈ components) (hright : right ∈ components)
    (hel : external ≠ left) (her : external ≠ right)
    (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    IsMaxOverlap external.text (left.merge right k).text
      (weight external.last (left.merge right k).first) := by
  have hbound := hglobal (mem_componentWords hexternal)
    (mem_componentWords hright) (state.text_ne hexternal hright her)
  simpa using (left_maxOverlap_interface hoverlap hbound).mpr
    (state.interface hexternal hleft hel)

variable [DecidableEq ι] [DecidableEq α]

/-- The path-state invariant is preserved by one globally maximal literal
merge of two distinct current components. -/
theorem afterMerge
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    PathState weight (replaceComponents components left right k) := by
  have hwords := componentWords_replaceComponents state.reduced.1
    hleft hright hne (k := k)
  have hleftWord := mem_componentWords hleft
  have hrightWord := mem_componentWords hright
  have hnextReduced :
      Reduced (componentWords (replaceComponents components left right k)) := by
    rw [hwords]
    exact replaceMerge_reduced state.reduced hoverlap hglobal
      hleftWord hrightWord
  have hcomponents := state.components_nodup
  have hmembership : ∀ component : PathComponent ι α,
      component ∈ replaceComponents components left right k ↔
        AfterComponentMerge components left right k component := by
    intro component
    exact mem_replaceComponents_iff_after
      (left := left) (right := right) (component := component)
      (k := k) hcomponents
  refine ⟨hnextReduced, ?_, ?_, ?_⟩
  · intro component hcomponent
    rcases (hmembership component).mp hcomponent with hmerge | hold
    · subst component
      rw [PathComponent.labels_merge]
      exact nodup_append_of_disjoint
        (state.labels_nodup hleft) (state.labels_nodup hright)
        (state.labels_disjoint hleft hright hne)
    · exact state.labels_nodup hold.1
  · intro first hfirst second hsecond hneNew
    rcases (hmembership first).mp hfirst with hfirstMerge | hfirstOld
    · subst first
      rcases (hmembership second).mp hsecond with hsecondMerge | hsecondOld
      · subst second
        exact (hneNew rfl).elim
      · rw [PathComponent.labels_merge, List.disjoint_append_left]
        exact ⟨state.labels_disjoint hleft hsecondOld.1 hsecondOld.2.1.symm,
          state.labels_disjoint hright hsecondOld.1 hsecondOld.2.2.symm⟩
    · rcases (hmembership second).mp hsecond with hsecondMerge | hsecondOld
      · subst second
        rw [PathComponent.labels_merge, List.disjoint_append_right]
        exact ⟨state.labels_disjoint hfirstOld.1 hleft hfirstOld.2.1,
          state.labels_disjoint hfirstOld.1 hright hfirstOld.2.2⟩
      · exact state.labels_disjoint hfirstOld.1 hsecondOld.1 hneNew
  · intro first hfirst second hsecond hneNew
    rcases (hmembership first).mp hfirst with hfirstMerge | hfirstOld
    · subst first
      rcases (hmembership second).mp hsecond with hsecondMerge | hsecondOld
      · subst second
        exact (hneNew rfl).elim
      · exact state.merged_outgoing_interface hleft hright hsecondOld.1
          hsecondOld.2.1.symm hsecondOld.2.2.symm hoverlap hglobal
    · rcases (hmembership second).mp hsecond with hsecondMerge | hsecondOld
      · subst second
        exact state.merged_incoming_interface hfirstOld.1 hleft hright
          hfirstOld.2.1 hfirstOld.2.2 hoverlap hglobal
      · exact state.interface hfirstOld.1 hsecondOld.1 hneNew

/-- The length drop rewritten with the original last-to-first edge weight. -/
theorem renderedLength_afterMerge_add
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    renderedLength (replaceComponents components left right k) +
        weight left.last right.first = renderedLength components := by
  have hk := state.selectedOverlap_eq hleft hright hne hoverlap hglobal
  have hlength := renderedLength_replaceComponents_add
    hleft hright hne hoverlap
  omega

theorem renderedLength_afterMerge
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    renderedLength (replaceComponents components left right k) =
      renderedLength components - weight left.last right.first := by
  have h := state.renderedLength_afterMerge_add
    hleft hright hne hoverlap hglobal
  omega

end PathState

/-- All facts needed to continue the path-state induction after one merge. -/
structure PathMergeUpdate [DecidableEq ι] [DecidableEq α]
    (weight : ι → ι → Nat)
    (components : List (PathComponent ι α))
    (left right : PathComponent ι α) (k : Nat) : Prop where
  labels_concat : (left.merge right k).labels = left.labels ++ right.labels
  first_eq : (left.merge right k).first = left.first
  last_eq : (left.merge right k).last = right.last
  selected_eq : k = weight left.last right.first
  words_eq :
    componentWords (replaceComponents components left right k) =
      replaceMerge (componentWords components) left.text right.text k
  next_state : PathState weight (replaceComponents components left right k)
  rendered_length_add :
    renderedLength (replaceComponents components left right k) +
      weight left.last right.first = renderedLength components

namespace PathState

variable [DecidableEq ι] [DecidableEq α]

/-- Induction-ready one-step package for a globally maximal component
merge. -/
theorem update
    {weight : ι → ι → Nat}
    {components : List (PathComponent ι α)}
    (state : PathState weight components)
    {left right : PathComponent ι α} {k : Nat}
    (hleft : left ∈ components) (hright : right ∈ components)
    (hne : left ≠ right) (hoverlap : IsOverlap left.text right.text k)
    (hglobal : GloballyMaximal (componentWords components) k) :
    PathMergeUpdate weight components left right k := by
  refine ⟨PathComponent.labels_merge _ _ _, rfl,
    PathComponent.last_merge _ _ _, ?_, ?_, ?_, ?_⟩
  · exact state.selectedOverlap_eq hleft hright hne hoverlap hglobal
  · exact componentWords_replaceComponents state.reduced.1
      hleft hright hne
  · exact state.afterMerge hleft hright hne hoverlap hglobal
  · exact state.renderedLength_afterMerge_add
      hleft hright hne hoverlap hglobal

end PathState

end State

end GreedySuperstring
