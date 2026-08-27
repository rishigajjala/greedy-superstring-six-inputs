import GreedySuperstring.Relaxation

/-!
# From a shortest common word to an exact Hamiltonian path

The occurrence-order theorem in `Optimal` constructs a maximum-overlap path
through a start-sorted permutation of a reduced family.  This module lifts
that word permutation back to the collision-free `Fin n` labels of a
`WordInstance` and packages the result as a `HamiltonianOrder`.
-/

namespace GreedySuperstring

/-- Every two finite words have an exact maximum suffix-prefix overlap. -/
theorem exists_maximum_overlap (left right : Word α) :
    ∃ k, IsMaxOverlap left right k := by
  classical
  let k := Nat.findGreatest (IsOverlap left right) left.length
  refine ⟨k, ?_, ?_⟩
  · exact Nat.findGreatest_spec (Nat.zero_le left.length)
      (overlap_zero left right)
  · intro r hr
    exact Nat.le_findGreatest hr.1 hr

/-- A canonical, classical choice of an exact maximum overlap. -/
noncomputable def maximumOverlapLength (left right : Word α) : ℕ :=
  Classical.choose (exists_maximum_overlap left right)

theorem maximumOverlapLength_spec (left right : Word α) :
    IsMaxOverlap left right (maximumOverlapLength left right) :=
  Classical.choose_spec (exists_maximum_overlap left right)

namespace OverlapPath

/-- Maximum-overlap paths on the same ordered word list have the same total
overlap saving, independently of which maximum witnesses were chosen. -/
theorem overlapSum_eq_of_hasMaximum
    {left right : OverlapPath α head rest}
    (leftMaximum : HasMaximumOverlaps left)
    (rightMaximum : HasMaximumOverlaps right) :
    left.overlapSum = right.overlapSum := by
  induction left with
  | nil head =>
      cases right
      rfl
  | @cons head next rest k overlap tail ih =>
      cases right with
      | cons r rightOverlap rightTail =>
          have hkr : k = r := maxOverlap_unique
            ⟨overlap, leftMaximum.1⟩ ⟨rightOverlap, rightMaximum.1⟩
          subst r
          simp only [overlapSum, overlapLengths_cons, List.sum_cons]
          exact congrArg (k + ·) (ih leftMaximum.2 rightMaximum.2)

end OverlapPath

namespace Relaxation

open OverlapPath

/-- The chosen `common` word has minimum length among all words containing
every labelled input.  Uniqueness of the shortest word is not required. -/
def IsShortestCommonSuperstring (data : WordInstance α n) : Prop :=
  ∀ candidate : Word α,
    (∀ i, (data.word i).IsInfix candidate) →
    data.common.length ≤ candidate.length

/-- The collision-free input placements used by occurrence sorting. -/
def inputPlacements (data : WordInstance α n) :
    List (PlacedWord data.common) :=
  List.ofFn fun i => ⟨data.word i, data.occurrence i⟩

@[simp] theorem placementWords_inputPlacements (data : WordInstance α n) :
    placementWords (inputPlacements data) = List.ofFn data.word := by
  simp [inputPlacements, placementWords, List.map_ofFn, Function.comp_def]

private theorem pathOfPlacements_overlapSum_eq_pathWeight
    (data : WordInstance α n) [Nonempty (Fin n)]
    (first : PlacedWord data.common)
    (rest : List (PlacedWord data.common))
    (inRange :
      ∀ word ∈ first.1 :: placementWords rest,
        ∃ i, data.word i = word)
    (labelsNodup :
      (Function.invFun data.word first.1 ::
        (placementWords rest).map (Function.invFun data.word)).Nodup) :
    (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
        first rest).overlapSum =
      pathWeight data.overlap (Function.invFun data.word first.1)
        ((placementWords rest).map (Function.invFun data.word)) := by
  induction rest generalizing first with
  | nil =>
      rfl
  | cons next remaining ih =>
      let label : Word α → Fin n := Function.invFun data.word
      have hlist :
          placementWords (next :: remaining) =
            next.1 :: placementWords remaining := rfl
      have firstRange : ∃ i, data.word i = first.1 :=
        inRange first.1 (by simp)
      have nextRange : ∃ i, data.word i = next.1 :=
        inRange next.1 (by simp [hlist])
      have firstWord : data.word (label first.1) = first.1 :=
        Function.invFun_eq firstRange
      have nextWord : data.word (label next.1) = next.1 :=
        Function.invFun_eq nextRange
      have hlabelNe : label first.1 ≠ label next.1 := by
        have hnotMem := List.nodup_cons.mp labelsNodup |>.1
        intro heq
        apply hnotMem
        simp [hlist, label, heq]
      have dataMaximum :
          IsMaxOverlap first.1 next.1
            (data.overlap (label first.1) (label next.1)) := by
        simpa [firstWord, nextWord] using
          data.maximum (label first.1) (label next.1) hlabelNe
      have weightEq :
          maximumOverlapLength first.1 next.1 =
            data.overlap (label first.1) (label next.1) :=
        maxOverlap_unique (maximumOverlapLength_spec first.1 next.1)
          dataMaximum
      have tailRange :
          ∀ word ∈ next.1 :: placementWords remaining,
            ∃ i, data.word i = word := by
        intro word hword
        exact inRange word (by simpa [hlist] using List.mem_cons_of_mem first.1 hword)
      have tailNodup :
          (label next.1 ::
            (placementWords remaining).map label).Nodup := by
        simpa [hlist, label] using (List.nodup_cons.mp labelsNodup).2
      have tailEq := ih next tailRange tailNodup
      change
        maximumOverlapLength first.1 next.1 +
            (pathOfPlacements maximumOverlapLength
              maximumOverlapLength_spec next remaining).overlapSum =
          data.overlap (label first.1) (label next.1) +
            pathWeight data.overlap (label next.1)
              ((placementWords remaining).map label)
      calc
        maximumOverlapLength first.1 next.1 +
              (pathOfPlacements maximumOverlapLength
                maximumOverlapLength_spec next remaining).overlapSum =
            data.overlap (label first.1) (label next.1) +
              (pathOfPlacements maximumOverlapLength
                maximumOverlapLength_spec next remaining).overlapSum :=
          congrArg
            (· + (pathOfPlacements maximumOverlapLength
              maximumOverlapLength_spec next remaining).overlapSum)
            weightEq
        _ = data.overlap (label first.1) (label next.1) +
              pathWeight data.overlap (label next.1)
                ((placementWords remaining).map label) :=
          congrArg (data.overlap (label first.1) (label next.1) + ·)
            tailEq

/-- For a nonempty reduced instance, minimality of the supplied common word
produces a Hamiltonian label order whose literal maximum-overlap path has
exactly the supplied optimum length. -/
theorem exists_exact_hamiltonian_order
    (data : WordInstance α n) (hn : 0 < n)
    (shortest : IsShortestCommonSuperstring data) :
    ∃ order : HamiltonianOrder n,
      (order.toOverlapPath data).superstring.length = data.optimumLength := by
  classical
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let placements := inputPlacements data
  have placementsNe : placements ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp [placements, inputPlacements] at hlength
    omega
  have placementsReduced : Reduced (placementWords placements) := by
    simpa [placements] using data.reduced
  obtain ⟨first, rest, path, _ordered, placementPerm, wordPerm,
      pathEq, _maximum, _additive, pathLe⟩ :=
    exists_permuted_path_lower_bound placements placementsNe
      placementsReduced maximumOverlapLength maximumOverlapLength_spec
  subst path
  have sortedMem (i : Fin n) :
      data.word i ∈ first.1 :: placementWords rest := by
    apply wordPerm.mem_iff.mpr
    have hmem := data.word_mem i
    simp [placements] at hmem ⊢
  have pathCommon :
      ∀ i, (data.word i).IsInfix
        (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).superstring := by
    intro i
    exact (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
      first rest).mem_isInfix_superstring (sortedMem i)
  have commonLe :
      data.common.length ≤
        (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).superstring.length :=
    shortest _ pathCommon
  have pathExact :
      (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).superstring.length = data.optimumLength := by
    exact Nat.le_antisymm pathLe commonLe
  let label : Word α → Fin n := Function.invFun data.word
  have inRange :
      ∀ word ∈ first.1 :: placementWords rest,
        ∃ i, data.word i = word := by
    intro word hword
    have horiginal := wordPerm.mem_iff.mp hword
    simpa [placements] using horiginal
  have rightLabelMap :
      (List.ofFn data.word).map label = List.ofFn id := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact Function.leftInverse_invFun data.word_injective i
  have labelPerm :
      (label first.1 :: (placementWords rest).map label).Perm
        (List.ofFn id) := by
    have mapped := wordPerm.map label
    have placementWordsEq :
        placementWords placements = List.ofFn data.word := by
      simp [placements]
    rw [placementWordsEq, rightLabelMap] at mapped
    simpa only [List.map_cons] using mapped
  have labelsNodup :
      (label first.1 :: (placementWords rest).map label).Nodup := by
    apply labelPerm.nodup_iff.mpr
    exact List.nodup_ofFn.mpr Function.injective_id
  have pathOverlapEq :
      (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).overlapSum =
        pathWeight data.overlap (label first.1)
          ((placementWords rest).map label) := by
    simpa [label] using
      pathOfPlacements_overlapSum_eq_pathWeight data first rest
        inRange labelsNodup
  let order : HamiltonianOrder n :=
    { head := label first.1
      rest := (placementWords rest).map label
      perm := labelPerm }
  have orderOverlapEq :
      (order.toOverlapPath data).overlapSum =
        (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).overlapSum := by
    calc
      (order.toOverlapPath data).overlapSum = order.overlapWeight data :=
        order.toOverlapPath_overlapSum data
      _ = pathWeight data.overlap (label first.1)
          ((placementWords rest).map label) := by
        rfl
      _ = (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
          first rest).overlapSum := pathOverlapEq.symm
  have pathTotal :
      totalWordLength first.1 (placementWords rest) =
        data.totalInputLength := by
    have hsum := (wordPerm.map (fun word : Word α => word.length)).sum_eq
    simpa [totalWordLength, WordInstance.totalInputLength,
      WordInstance.inputLength, placements, List.map_ofFn,
      Function.comp_def] using hsum
  have orderAdd := (order.toOverlapPath data).length_add_overlapSum
  have orderTotal := order.totalWordLength_eq_totalInputLength data
  rw [orderTotal] at orderAdd
  have pathAdd :=
    (pathOfPlacements maximumOverlapLength maximumOverlapLength_spec
      first rest).length_add_overlapSum
  rw [pathTotal] at pathAdd
  refine ⟨order, ?_⟩
  rw [WordInstance.optimumLength]
  omega

end Relaxation

end GreedySuperstring
