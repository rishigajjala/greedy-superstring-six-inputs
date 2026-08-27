import GreedySuperstring.Word

/-!
# Literal greedy superstring runs

This module connects the literal word model to an actual greedy execution.  A
step removes two distinct current words and inserts their overlap merge.  The
relation records both the chosen overlap and its global maximality among the
current words; its reflexive-transitive closure is a complete greedy run.
-/

namespace GreedySuperstring

section

variable {α : Type u} [DecidableEq α]

/-- Remove the two selected words and put their merge at the head. -/
def replaceMerge (S : List (Word α)) (a b : Word α) (k : Nat) :
    List (Word α) :=
  mergeAt a b k :: (S.erase a).erase b

/-- On a duplicate-free state, membership in the concrete replacement list is
exactly the abstract `AfterMerge` predicate used by the word kernel. -/
theorem mem_replaceMerge_iff_afterMerge
    {S : List (Word α)} {a b x : Word α} {k : Nat}
    (hS : S.Nodup) :
    x ∈ replaceMerge S a b k ↔ AfterMerge S a b k x := by
  simp only [replaceMerge, List.mem_cons, AfterMerge]
  constructor
  · rintro (hmerge | htail)
    · exact Or.inl hmerge
    · have hbInfo := (hS.erase a).mem_erase_iff.mp htail
      have haInfo := hS.mem_erase_iff.mp hbInfo.2
      exact Or.inr ⟨haInfo.2, haInfo.1, hbInfo.1⟩
  · rintro (hmerge | ⟨hxS, hxa, hxb⟩)
    · exact Or.inl hmerge
    · exact Or.inr <| (hS.erase a).mem_erase_iff.mpr
        ⟨hxb, hS.mem_erase_iff.mpr ⟨hxa, hxS⟩⟩

/-- Replacing two distinct members by their merge removes exactly one list
entry. -/
theorem replaceMerge_length
    {S : List (Word α)} {a b : Word α} {k : Nat}
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    (replaceMerge S a b k).length = S.length - 1 := by
  have hb' : b ∈ S.erase a := (List.mem_erase_of_ne hne.symm).2 hb
  have hlenA := List.length_erase_of_mem ha
  have hlenB := List.length_erase_of_mem hb'
  have hpos : 0 < (S.erase a).length := List.length_pos_of_mem hb'
  simp only [replaceMerge, List.length_cons]
  omega

theorem replaceMerge_length_lt
    {S : List (Word α)} {a b : Word α} {k : Nat}
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    (replaceMerge S a b k).length < S.length := by
  have hlen := replaceMerge_length (k := k) ha hb hne
  have hpos : 0 < S.length := List.length_pos_of_mem ha
  omega

/-- The global-overlap crossing lemma from `Word` rules out both a duplicate
merge and every new infix comparison. -/
theorem replaceMerge_nodup
    {S : List (Word α)} {a b : Word α} {k : Nat}
    (hred : Reduced S) (hab : IsOverlap a b k)
    (hglobal : GloballyMaximal S k) (ha : a ∈ S) (hb : b ∈ S) :
    (replaceMerge S a b k).Nodup := by
  rw [replaceMerge, List.nodup_cons]
  constructor
  · intro hm
    have hbInfo := (hred.1.erase a).mem_erase_iff.mp hm
    have haInfo := hred.1.mem_erase_iff.mp hbInfo.2
    have hbad := (old_word_incomparable_with_global_merge
      hred hab hglobal ha hb haInfo.2 haInfo.1 hbInfo.1).2
    exact hbad ⟨[], [], by simp⟩
  · exact (hred.1.erase a).erase b

/-- A legal greedy replacement preserves the reduced-state invariant. -/
theorem replaceMerge_reduced
    {S : List (Word α)} {a b : Word α} {k : Nat}
    (hred : Reduced S) (hab : IsOverlap a b k)
    (hglobal : GloballyMaximal S k) (ha : a ∈ S) (hb : b ∈ S) :
    Reduced (replaceMerge S a b k) := by
  refine ⟨replaceMerge_nodup hred hab hglobal ha hb, ?_⟩
  intro x y hx hy hxy
  exact globallyMaximal_merge_preserves_antichain
    hred hab hglobal ha hb
    ((mem_replaceMerge_iff_afterMerge hred.1).mp hx)
    ((mem_replaceMerge_iff_afterMerge hred.1).mp hy) hxy

/-- One literal greedy step.  The selected overlap must be globally maximal in
the current state, including ties. -/
inductive GreedyStep (S T : List (Word α)) : Prop where
  | mk (left right : Word α) (overlapLength : Nat)
      (left_mem : left ∈ S) (right_mem : right ∈ S)
      (distinct : left ≠ right)
      (overlap : IsOverlap left right overlapLength)
      (global : GloballyMaximal S overlapLength)
      (target_eq : T = replaceMerge S left right overlapLength) :
      GreedyStep S T

/-- The reflexive-transitive closure of literal greedy steps. -/
inductive GreedyRun : List (Word α) → List (Word α) → Prop where
  | refl (S : List (Word α)) : GreedyRun S S
  | tail {S T U : List (Word α)} :
      GreedyRun S T → GreedyStep T U → GreedyRun S U

/-- Every word in the first state occurs as an infix of some word in the
second state. -/
def Covers (S T : List (Word α)) : Prop :=
  ∀ ⦃w⦄, w ∈ S → ∃ t ∈ T, w.IsInfix t

theorem replaceMerge_covers
    {S : List (Word α)} {a b : Word α} {k : Nat}
    (hab : IsOverlap a b k) :
    Covers S (replaceMerge S a b k) := by
  intro w hw
  by_cases hwa : w = a
  · subst w
    exact ⟨mergeAt a b k, by simp [replaceMerge],
      left_isInfix_mergeAt a b k⟩
  by_cases hwb : w = b
  · subst w
    exact ⟨mergeAt a b k, by simp [replaceMerge],
      right_isInfix_mergeAt hab⟩
  · refine ⟨w, ?_, ⟨[], [], by simp⟩⟩
    simp only [replaceMerge, List.mem_cons]
    exact Or.inr <| (List.mem_erase_of_ne hwb).2
      ((List.mem_erase_of_ne hwa).2 hw)

namespace Covers

omit [DecidableEq α] in
theorem refl (S : List (Word α)) : Covers S S := by
  intro w hw
  exact ⟨w, hw, ⟨[], [], by simp⟩⟩

omit [DecidableEq α] in
theorem trans {S T U : List (Word α)}
    (hST : Covers S T) (hTU : Covers T U) : Covers S U := by
  intro w hw
  rcases hST hw with ⟨t, ht, hwt⟩
  rcases hTU ht with ⟨u, hu, htu⟩
  exact ⟨u, hu, hwt.trans htu⟩

end Covers

namespace GreedyStep

theorem preservesReduced {S T : List (Word α)}
    (step : GreedyStep S T) (hred : Reduced S) : Reduced T := by
  rcases step with ⟨a, b, k, ha, hb, _, hab, hglobal, hT⟩
  rw [hT]
  exact replaceMerge_reduced hred hab hglobal ha hb

theorem length_eq {S T : List (Word α)} (step : GreedyStep S T) :
    T.length = S.length - 1 := by
  rcases step with ⟨a, b, k, ha, hb, hne, _, _, hT⟩
  rw [hT]
  exact replaceMerge_length ha hb hne

theorem length_lt {S T : List (Word α)} (step : GreedyStep S T) :
    T.length < S.length := by
  rcases step with ⟨a, b, k, ha, hb, hne, _, _, hT⟩
  rw [hT]
  exact replaceMerge_length_lt ha hb hne

theorem covers {S T : List (Word α)} (step : GreedyStep S T) : Covers S T := by
  rcases step with ⟨a, b, k, ha, hb, hne, hab, _, hT⟩
  rw [hT]
  exact replaceMerge_covers hab

end GreedyStep

namespace GreedyRun

theorem covers {S T : List (Word α)} (run : GreedyRun S T) : Covers S T := by
  induction run with
  | refl => exact Covers.refl S
  | tail run step ih => exact Covers.trans ih step.covers

theorem preservesReduced {S T : List (Word α)}
    (run : GreedyRun S T) (hred : Reduced S) : Reduced T := by
  induction run with
  | refl => exact hred
  | tail run step ih => exact step.preservesReduced ih

theorem length_le {S T : List (Word α)} (run : GreedyRun S T) :
    T.length ≤ S.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail run step ih => exact Nat.le_trans step.length_lt.le ih

/-- If a run ends in one word, every original word is an infix of that final
word. -/
theorem infix_of_final_singleton {S T : List (Word α)} {g w : Word α}
    (run : GreedyRun S T) (hT : T = [g]) (hw : w ∈ S) : w.IsInfix g := by
  rcases run.covers hw with ⟨t, ht, hwt⟩
  rw [hT] at ht
  simp only [List.mem_singleton] at ht
  subst t
  exact hwt

end GreedyRun

end

end GreedySuperstring
