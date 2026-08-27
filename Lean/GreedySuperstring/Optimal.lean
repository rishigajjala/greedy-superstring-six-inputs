import GreedySuperstring.Word
import Mathlib.Data.List.Sort

/-!
# Constructive Hamiltonian-path superstrings

An `OverlapPath` is a nonempty ordered list of words together with a certified
suffix-prefix overlap for every adjacent pair. This file constructs the
literal superstring represented by such a path and proves containment and the
telescoping length identity.
-/

namespace GreedySuperstring

/-- A nonempty ordered path of words with one certified overlap per adjacent
pair. The head word is an index, so the empty path is not representable. -/
inductive OverlapPath (α : Type u) : Word α → List (Word α) → Type u where
  | nil (head : Word α) : OverlapPath α head []
  | cons {head next : Word α} {rest : List (Word α)}
      (k : ℕ) (overlap : IsOverlap head next k)
      (tail : OverlapPath α next rest) :
      OverlapPath α head (next :: rest)

namespace OverlapPath

variable {α : Type u} {head : Word α} {rest : List (Word α)}

/-- Material appended after the head word. -/
def additions {head : Word α} {rest : List (Word α)}
    (path : OverlapPath α head rest) : Word α :=
  match path with
  | .nil _ => []
  | .cons (next := next) k _ tail => next.drop k ++ additions tail

/-- Literal superstring obtained by following the path in order. -/
def superstring (path : OverlapPath α head rest) : Word α :=
  head ++ additions path

/-- Stored adjacent-overlap lengths in path order. -/
def overlapLengths {head : Word α} {rest : List (Word α)}
    (path : OverlapPath α head rest) : List ℕ :=
  match path with
  | .nil _ => []
  | .cons k _ tail => k :: overlapLengths tail

/-- Sum of the stored adjacent-overlap lengths. -/
def overlapSum (path : OverlapPath α head rest) : ℕ :=
  path.overlapLengths.sum

/-- Sum of the lengths of all words in a nonempty ordered list. -/
def totalWordLength (head : Word α) (rest : List (Word α)) : ℕ :=
  head.length + (rest.map (fun word => word.length)).sum

@[simp] theorem additions_nil (head : Word α) :
    additions (.nil head) = [] := rfl

@[simp] theorem additions_cons {next : Word α} {rest : List (Word α)}
    {k : ℕ} {overlap : IsOverlap head next k}
    {tail : OverlapPath α next rest} :
    additions (.cons k overlap tail) = next.drop k ++ additions tail := rfl

@[simp] theorem overlapLengths_nil (head : Word α) :
    overlapLengths (.nil head) = [] := rfl

@[simp] theorem overlapLengths_cons {next : Word α} {rest : List (Word α)}
    {k : ℕ} {overlap : IsOverlap head next k}
    {tail : OverlapPath α next rest} :
    overlapLengths (.cons k overlap tail) = k :: overlapLengths tail := rfl

/-- The head word is a prefix, hence an infix, of the rendered path. -/
theorem head_isPrefix_superstring (path : OverlapPath α head rest) :
    head.IsPrefix path.superstring := by
  exact ⟨path.additions, rfl⟩

theorem head_isInfix_superstring (path : OverlapPath α head rest) :
    head.IsInfix path.superstring :=
  path.head_isPrefix_superstring.isInfix

/-- In a nontrivial path, the superstring rendered from the tail is a suffix
of the superstring rendered from the whole path. -/
theorem tail_superstring_isSuffix {next : Word α} {rest : List (Word α)}
    {k : ℕ} (overlap : IsOverlap head next k)
    (tail : OverlapPath α next rest) :
    tail.superstring.IsSuffix (superstring (.cons k overlap tail)) := by
  rcases right_isSuffix_mergeAt overlap with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  calc
    pre ++ tail.superstring = (pre ++ next) ++ tail.additions := by
      simp [superstring, List.append_assoc]
    _ = mergeAt head next k ++ tail.additions := by rw [hpre]
    _ = superstring (.cons k overlap tail) := by
      simp [superstring, mergeAt, List.append_assoc]

/-- Every word listed by the path occurs in its rendered superstring. -/
theorem mem_isInfix_superstring (path : OverlapPath α head rest)
    {word : Word α} (hmem : word ∈ head :: rest) :
    word.IsInfix path.superstring := by
  induction path with
  | nil head =>
      have hw : word = head := by simpa using hmem
      subst word
      exact head_isInfix_superstring (.nil head)
  | @cons head next rest k overlap tail ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact head_isInfix_superstring (.cons k overlap tail)
      · exact (ih htail).trans (tail_superstring_isSuffix overlap tail).isInfix

/-- Additive telescoping identity. This form avoids truncated subtraction:
rendered length plus all overlaps equals the sum of all input lengths. -/
theorem length_add_overlapSum (path : OverlapPath α head rest) :
    path.superstring.length + path.overlapSum = totalWordLength head rest := by
  induction path with
  | nil head =>
      simp [superstring, overlapSum, totalWordLength]
  | @cons head next rest k overlap tail ih =>
      have hk : k ≤ next.length := overlap.2.1
      simp [superstring, overlapSum, totalWordLength, List.length_drop] at ih ⊢
      omega

/-- Subtractive form of the telescoping path length formula. -/
theorem superstring_length (path : OverlapPath α head rest) :
    path.superstring.length = totalWordLength head rest - path.overlapSum := by
  have h := path.length_add_overlapSum
  omega

end OverlapPath

end GreedySuperstring


namespace GreedySuperstring

/-- One chosen occurrence of `word` inside `common`. -/
structure Occurrence (word common : Word α) where
  before : Word α
  after : Word α
  decomposition : before ++ word ++ after = common

namespace Occurrence

variable {word common : Word α}

/-- Starting position of the chosen occurrence. -/
def start (occurrence : Occurrence word common) : ℕ :=
  occurrence.before.length

/-- Position immediately after the chosen occurrence. -/
def finish (occurrence : Occurrence word common) : ℕ :=
  occurrence.start + word.length

theorem finish_le_common_length (occurrence : Occurrence word common) :
    occurrence.finish ≤ common.length := by
  have hlength := congrArg List.length occurrence.decomposition
  simp [finish, start] at hlength ⊢
  omega

end Occurrence

namespace OverlapPath

variable {α : Type u} {head : Word α} {rest : List (Word α)}
  {common : Word α}

/-- Every stored overlap is maximal for its adjacent ordered pair. -/
def HasMaximumOverlaps : {head : Word α} → {rest : List (Word α)} →
    OverlapPath α head rest → Prop
  | _, _, .nil _ => True
  | _, _, .cons (head := head) (next := next) k _ tail =>
      OverlapLE head next k ∧ HasMaximumOverlaps tail

@[simp] theorem hasMaximumOverlaps_nil (head : Word α) :
    HasMaximumOverlaps (.nil head) := trivial

@[simp] theorem hasMaximumOverlaps_cons {next : Word α}
    {rest : List (Word α)} {k : ℕ} {overlap : IsOverlap head next k}
    {tail : OverlapPath α next rest} :
    HasMaximumOverlaps (.cons k overlap tail) ↔
      OverlapLE head next k ∧ HasMaximumOverlaps tail := Iff.rfl

/-- Chosen occurrences aligned with a path, ordered by nondecreasing starts
and nondecreasing finishes.  The first occurrence is an index, ensuring that
the recursive tail begins with exactly the chosen occurrence for `next`. -/
inductive OrderedOccurrences (common : Word α) :
    {head : Word α} → {rest : List (Word α)} →
    (path : OverlapPath α head rest) → Occurrence head common → Type u where
  | nil {head : Word α} (headOccurrence : Occurrence head common) :
      OrderedOccurrences common (.nil head) headOccurrence
  | cons {head next : Word α} {rest : List (Word α)}
      {k : ℕ} {overlap : IsOverlap head next k}
      {tail : OverlapPath α next rest}
      (headOccurrence : Occurrence head common)
      (nextOccurrence : Occurrence next common)
      (tailOccurrences : OrderedOccurrences common tail nextOccurrence)
      (start_le : headOccurrence.start ≤ nextOccurrence.start)
      (finish_le : headOccurrence.finish ≤ nextOccurrence.finish) :
      OrderedOccurrences common (.cons k overlap tail) headOccurrence

/-- The geometric overlap of two ordered occurrences forces the next start
displacement to be at least `|head| - k` when `k` is a maximum overlap. -/
theorem adjacent_start_displacement_ge
    {next : Word α} {k : ℕ}
    (maximum : OverlapLE head next k)
    (headOccurrence : Occurrence head common)
    (nextOccurrence : Occurrence next common)
    (start_le : headOccurrence.start ≤ nextOccurrence.start)
    (finish_le : headOccurrence.finish ≤ nextOccurrence.finish) :
    head.length - k ≤ nextOccurrence.start - headOccurrence.start := by
  have geometric : IsOverlap head next
      (head.length - (nextOccurrence.start - headOccurrence.start)) := by
    apply ordered_occurrences_overlap_witness
        headOccurrence.decomposition nextOccurrence.decomposition
    · exact start_le
    · simpa [Occurrence.finish, Occurrence.start] using finish_le
  have hle := maximum _ geometric
  omega

/-- Strengthened telescoping lower bound.  The first occurrence start is kept
on the left so recursive adjacent displacements cancel exactly. -/
theorem OrderedOccurrences.totalWordLength_add_start_le
    {path : OverlapPath α head rest} {headOccurrence : Occurrence head common}
    (ordered : OrderedOccurrences common path headOccurrence)
    (maximum : HasMaximumOverlaps path) :
    totalWordLength head rest + headOccurrence.start ≤
      common.length + path.overlapSum := by
  induction ordered with
  | nil headOccurrence =>
      have hend := headOccurrence.finish_le_common_length
      simp [totalWordLength, overlapSum, Occurrence.finish] at hend ⊢
      omega
  | @cons head next rest k overlap tail headOccurrence nextOccurrence
      tailOccurrences start_le finish_le ih =>
      have hmaximum : OverlapLE head next k := maximum.1
      have htailMaximum : HasMaximumOverlaps tail := maximum.2
      have hadj := adjacent_start_displacement_ge hmaximum headOccurrence
        nextOccurrence start_le finish_le
      have htail := ih htailMaximum
      simp only [totalWordLength, List.map_cons, List.sum_cons,
        overlapSum, overlapLengths_cons, List.sum_cons] at htail ⊢
      omega

/-- Ordered-occurrence lower bound in the manuscript's additive form. -/
theorem OrderedOccurrences.totalWordLength_le_common_add_overlapSum
    {path : OverlapPath α head rest} {headOccurrence : Occurrence head common}
    (ordered : OrderedOccurrences common path headOccurrence)
    (maximum : HasMaximumOverlaps path) :
    totalWordLength head rest ≤ common.length + path.overlapSum := by
  have h := ordered.totalWordLength_add_start_le maximum
  omega

/-- Any common word carrying ordered, nonnested path occurrences is at least
as long as the literal path superstring. -/
theorem OrderedOccurrences.superstring_length_le_common
    {path : OverlapPath α head rest} {headOccurrence : Occurrence head common}
    (ordered : OrderedOccurrences common path headOccurrence)
    (maximum : HasMaximumOverlaps path) :
    path.superstring.length ≤ common.length := by
  have hlower := ordered.totalWordLength_add_start_le maximum
  have hpath := path.length_add_overlapSum
  omega

end OverlapPath

end GreedySuperstring

namespace GreedySuperstring

namespace Occurrence


variable {α : Type u} {x y common : Word α}

private theorem prefix_after_start (occurrence : Occurrence x common) :
    x.IsPrefix (common.drop occurrence.start) := by
  refine ⟨occurrence.after, ?_⟩
  calc
    x ++ occurrence.after =
        (occurrence.before ++ x ++ occurrence.after).drop occurrence.before.length := by
          simp [List.append_assoc]
    _ = common.drop occurrence.before.length :=
      congrArg (List.drop occurrence.before.length) occurrence.decomposition

private theorem remainder_prefix_at
    (occurrence : Occurrence x common) {position : ℕ}
    (hstart : occurrence.start ≤ position) :
    (x.drop (position - occurrence.start)).IsPrefix (common.drop position) := by
  have hp : (occurrence.before ++ x).IsPrefix common :=
    ⟨occurrence.after, occurrence.decomposition⟩
  have hd := hp.drop position
  have heq : (occurrence.before ++ x).drop position =
      x.drop (position - occurrence.start) := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by simpa [start] using hstart)]
    simp [start]
  rw [heq] at hd
  exact hd

private theorem prefix_of_common_prefix {a b t : List α}
    (ha : a.IsPrefix t) (hb : b.IsPrefix t) (hlen : a.length ≤ b.length) :
    a.IsPrefix b := by
  rw [List.prefix_iff_eq_take] at ha hb ⊢
  calc
    a = t.take a.length := ha
    _ = (t.take b.length).take a.length := by
      rw [List.take_take]
      simp [Nat.min_eq_left hlen]
    _ = b.take a.length := (congrArg (List.take a.length) hb).symm

/-- For substring-incomparable words, ordering chosen occurrences by start
also orders their finishes. -/
theorem finish_le_of_start_le_of_not_infix
    (xOccurrence : Occurrence x common) (yOccurrence : Occurrence y common)
    (hstart : xOccurrence.start ≤ yOccurrence.start)
    (hnot : ¬y.IsInfix x) :
    xOccurrence.finish ≤ yOccurrence.finish := by
  apply Nat.le_of_not_gt
  intro hfinish
  let d := yOccurrence.start - xOccurrence.start
  have hxTail : (x.drop d).IsPrefix (common.drop yOccurrence.start) :=
    remainder_prefix_at xOccurrence hstart
  have hyTail : y.IsPrefix (common.drop yOccurrence.start) :=
    prefix_after_start yOccurrence
  have hylen : y.length ≤ (x.drop d).length := by
    simp [d, finish] at hfinish ⊢
    omega
  have hyPrefix : y.IsPrefix (x.drop d) :=
    prefix_of_common_prefix hyTail hxTail hylen
  exact hnot (hyPrefix.isInfix.trans (List.drop_suffix d x).isInfix)

end Occurrence

/-- A word paired with one chosen occurrence in `common`. -/
abbrev PlacedWord (common : Word α) :=
  Σ word : Word α, Occurrence word common

/-- Forget the occurrences and retain the ordered words. -/
def placementWords {common : Word α} (placements : List (PlacedWord common)) :
    List (Word α) :=
  placements.map (fun placement => placement.1)

private def placementStartLE {common : Word α}
    (left right : PlacedWord common) : Bool :=
  decide (left.2.start ≤ right.2.start)

/-- Sort chosen word occurrences by nondecreasing start. -/
def sortPlacements {common : Word α} (placements : List (PlacedWord common)) :
    List (PlacedWord common) :=
  placements.mergeSort placementStartLE

theorem sortPlacements_perm {common : Word α}
    (placements : List (PlacedWord common)) :
    (sortPlacements placements).Perm placements := by
  exact List.mergeSort_perm placements placementStartLE

theorem sortedWords_perm {common : Word α}
    (placements : List (PlacedWord common)) :
    placementWords (sortPlacements placements) |>.Perm (placementWords placements) := by
  exact (sortPlacements_perm placements).map (fun placement => placement.1)

theorem sortPlacements_pairwise_start {common : Word α}
    (placements : List (PlacedWord common)) :
    (sortPlacements placements).Pairwise
      (fun left right => left.2.start ≤ right.2.start) := by
  have hsorted := List.pairwise_mergeSort
    (le := placementStartLE)
    (fun a b c hab hbc => by
      simp [placementStartLE] at hab hbc ⊢
      omega)
    (fun a b => by
      simp [placementStartLE]
      omega)
    placements
  simpa [sortPlacements, placementStartLE] using hsorted

/-- Reducedness rules out reversed finishes in the start-sorted list. -/
theorem sortPlacements_pairwise_finish {common : Word α}
    (placements : List (PlacedWord common))
    (hred : Reduced (placementWords placements)) :
    (sortPlacements placements).Pairwise
      (fun left right => left.2.finish ≤ right.2.finish) := by
  let sorted := sortPlacements placements
  have hpermWords : placementWords sorted |>.Perm (placementWords placements) := by
    exact sortedWords_perm placements
  have hnodupWords : (placementWords sorted).Nodup :=
    hpermWords.nodup_iff.mpr hred.1
  have hwordNe : sorted.Pairwise (fun left right => left.1 ≠ right.1) := by
    exact List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hnodupWords)
  have hstarts : sorted.Pairwise
      (fun left right => left.2.start ≤ right.2.start) := by
    exact sortPlacements_pairwise_start placements
  apply (hstarts.and hwordNe).imp_of_mem
  intro left right hleft hright hrel
  have hleftWord : left.1 ∈ placementWords placements := by
    apply hpermWords.mem_iff.mp
    exact List.mem_map.mpr ⟨left, hleft, rfl⟩
  have hrightWord : right.1 ∈ placementWords placements := by
    apply hpermWords.mem_iff.mp
    exact List.mem_map.mpr ⟨right, hright, rfl⟩
  have hnot : ¬right.1.IsInfix left.1 :=
    hred.2 hrightWord hleftWord (Ne.symm hrel.2)
  exact Occurrence.finish_le_of_start_le_of_not_infix
    left.2 right.2 hrel.1 hnot

end GreedySuperstring

namespace GreedySuperstring

namespace OverlapPath

variable {α : Type u} {common : Word α}

/-- Attach supplied maximum-overlap certificates to a nonempty ordered list
of placed words. -/
def pathOfPlacements
    (weight : Word α → Word α → ℕ)
    (certificate : ∀ left right, IsMaxOverlap left right (weight left right))
    (first : PlacedWord common) (rest : List (PlacedWord common)) :
    OverlapPath α first.1 (placementWords rest) :=
  match rest with
  | [] => .nil first.1
  | next :: remaining =>
      .cons (weight first.1 next.1) (certificate first.1 next.1).1
        (pathOfPlacements weight certificate next remaining)

theorem pathOfPlacements_hasMaximum
    (weight : Word α → Word α → ℕ)
    (certificate : ∀ left right, IsMaxOverlap left right (weight left right))
    (first : PlacedWord common) (rest : List (PlacedWord common)) :
    HasMaximumOverlaps (pathOfPlacements weight certificate first rest) := by
  induction rest generalizing first with
  | nil =>
      exact trivial
  | cons next remaining ih =>
      rw [show pathOfPlacements weight certificate first (next :: remaining) =
        .cons (weight first.1 next.1) (certificate first.1 next.1).1
          (pathOfPlacements weight certificate next remaining) by rfl]
      exact ⟨(certificate first.1 next.1).2, ih next⟩

/-- Convert pairwise start/finish order into the recursive occurrence object
used by the lower-bound theorem. -/
def pathOfPlacements_ordered
    (weight : Word α → Word α → ℕ)
    (certificate : ∀ left right, IsMaxOverlap left right (weight left right))
    (first : PlacedWord common) (rest : List (PlacedWord common))
    (hstarts : (first :: rest).Pairwise
      (fun left right => left.2.start ≤ right.2.start))
    (hfinishes : (first :: rest).Pairwise
      (fun left right => left.2.finish ≤ right.2.finish)) :
    OrderedOccurrences common (pathOfPlacements weight certificate first rest)
      first.2 := by
  induction rest generalizing first with
  | nil =>
      exact .nil first.2
  | cons next remaining ih =>
      have hs := List.pairwise_cons.mp hstarts
      have hf := List.pairwise_cons.mp hfinishes
      have hstart : first.2.start ≤ next.2.start :=
        hs.1 next (by simp)
      have hfinish : first.2.finish ≤ next.2.finish :=
        hf.1 next (by simp)
      exact .cons first.2 next.2 (ih next hs.2 hf.2) hstart hfinish

/-- Lower-bound half of the Hamiltonian-path formula for a nonempty reduced
family with one chosen occurrence of every word in `common`.  It produces a
start-sorted permutation, attaches the supplied maximum overlaps, and proves
both the additive lower bound and comparison with the literal path word. -/
theorem exists_permuted_path_lower_bound
    (placements : List (PlacedWord common)) (hne : placements ≠ [])
    (hred : Reduced (placementWords placements))
    (weight : Word α → Word α → ℕ)
    (certificate : ∀ left right, IsMaxOverlap left right (weight left right)) :
    ∃ (first : PlacedWord common) (rest : List (PlacedWord common))
      (path : OverlapPath α first.1 (placementWords rest))
      (_ordered : OrderedOccurrences common path first.2),
      (first :: rest).Perm placements ∧
      (first.1 :: placementWords rest).Perm (placementWords placements) ∧
      path = pathOfPlacements weight certificate first rest ∧
      HasMaximumOverlaps path ∧
      totalWordLength first.1 (placementWords rest) ≤
        common.length + path.overlapSum ∧
      path.superstring.length ≤ common.length := by
  cases hsort : sortPlacements placements with
  | nil =>
      have hp : ([] : List (PlacedWord common)).Perm placements := by
        simpa [hsort] using sortPlacements_perm placements
      have hempty : placements = [] := by simpa using hp
      exact (hne hempty).elim
  | cons first rest =>
      let path := pathOfPlacements weight certificate first rest
      have hperm : (first :: rest).Perm placements := by
        simpa [hsort] using sortPlacements_perm placements
      have hwordPerm :
          (first.1 :: placementWords rest).Perm (placementWords placements) := by
        simpa [placementWords] using hperm.map (fun placement => placement.1)
      have hstarts : (first :: rest).Pairwise
          (fun left right => left.2.start ≤ right.2.start) := by
        simpa [hsort] using sortPlacements_pairwise_start placements
      have hfinishes : (first :: rest).Pairwise
          (fun left right => left.2.finish ≤ right.2.finish) := by
        simpa [hsort] using sortPlacements_pairwise_finish placements hred
      have hmaximum : HasMaximumOverlaps path :=
        pathOfPlacements_hasMaximum weight certificate first rest
      have hordered : OrderedOccurrences common path first.2 :=
        pathOfPlacements_ordered weight certificate first rest hstarts hfinishes
      have hadd := hordered.totalWordLength_le_common_add_overlapSum hmaximum
      have hlength := hordered.superstring_length_le_common hmaximum
      exact ⟨first, rest, path, hordered, hperm, hwordPerm, rfl, hmaximum,
        hadd, hlength⟩

end OverlapPath

end GreedySuperstring
