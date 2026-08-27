import GreedySuperstring.Optimal
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange

/-!
# Semantic facts for the finite overlap relaxation

This file packages an actual finite family of reduced words behind the dense
linear relaxation. Labels are `Fin n`, so an overlap coordinate cannot be
silently confused with a duplicate list position. All statements are kept
unnormalized over `Nat`, with integral row forms supplied where subtraction is
the natural LP notation.

Only chronology-independent facts live here: nonnegativity, length and
endpoint caps, directed triangles, pair rows, and the equality contributed by
an exact Hamiltonian path. Greedy chronology and dense coefficient arrays
belong to later layers.
-/

namespace GreedySuperstring.Relaxation

/-- Literal word data realizing one finite overlap-relaxation point. -/
structure WordInstance (α : Type u) (n : ℕ) where
  /-- The input word carrying each collision-free label. -/
  word : Fin n → Word α
  /-- A common superstring used as the unnormalized optimum parameter. -/
  common : Word α
  /-- The chosen directed maximum-overlap lengths. -/
  overlap : Fin n → Fin n → ℕ
  /-- The original family is a substring antichain and has no duplicates. -/
  reduced : Reduced (List.ofFn word)
  /-- Every off-diagonal overlap coordinate is its literal exact maximum. -/
  maximum : ∀ i j, i ≠ j → IsMaxOverlap (word i) (word j) (overlap i j)
  /-- One concrete occurrence of each input in the common superstring. -/
  occurrence : ∀ i, Occurrence (word i) common

namespace WordInstance

variable {α : Type u} {n : ℕ} (data : WordInstance α n)

/-- Unnormalized LP length coordinate. -/
def inputLength (i : Fin n) : ℕ :=
  (data.word i).length

/-- Unnormalized optimum coordinate. -/
def optimumLength : ℕ :=
  data.common.length

/-- Sum of all input-length coordinates. -/
def totalInputLength : ℕ :=
  (List.ofFn fun i => data.inputLength i).sum

theorem word_mem (i : Fin n) :
    data.word i ∈ List.ofFn data.word := by
  simp

/-- Reducedness makes the label-to-word map injective. -/
theorem word_injective : Function.Injective data.word := by
  exact List.nodup_ofFn.mp data.reduced.1

theorem word_ne {i j : Fin n} (hne : i ≠ j) :
    data.word i ≠ data.word j := by
  intro hij
  exact hne (data.word_injective hij)

/-- The chosen decomposition indeed witnesses substring containment. -/
theorem word_isInfix_common (i : Fin n) :
    (data.word i).IsInfix data.common := by
  let occurrence := data.occurrence i
  exact ⟨occurrence.before, occurrence.after, occurrence.decomposition⟩

/-- Nat nonnegativity row for an input length. -/
theorem inputLength_nonnegative (i : Fin n) :
    0 ≤ data.inputLength i :=
  Nat.zero_le _

/-- Nat nonnegativity row for a directed overlap. -/
theorem overlap_nonnegative (i j : Fin n) :
    0 ≤ data.overlap i j :=
  Nat.zero_le _

/-- Every input word fits inside the supplied common superstring. -/
theorem inputLength_le_optimumLength (i : Fin n) :
    data.inputLength i ≤ data.optimumLength := by
  have hfinish := (data.occurrence i).finish_le_common_length
  simp only [Occurrence.finish, inputLength, optimumLength] at hfinish ⊢
  omega

/-- Left endpoint cap for every off-diagonal overlap coordinate. -/
theorem overlap_le_source {i j : Fin n} (hne : i ≠ j) :
    data.overlap i j ≤ data.inputLength i := by
  exact (data.maximum i j hne).1.1

/-- Right endpoint cap for every off-diagonal overlap coordinate. -/
theorem overlap_le_target {i j : Fin n} (hne : i ≠ j) :
    data.overlap i j ≤ data.inputLength j := by
  exact (data.maximum i j hne).1.2.1

/-- Every directed overlap-distance triangle on three distinct labels. -/
theorem directed_triangle {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    data.overlap i j + data.overlap j k ≤
      data.inputLength j + data.overlap i k := by
  exact GreedySuperstring.directed_overlap_triangle
    (data.maximum i j hij).1
    (data.maximum j k hjk).1
    (data.maximum i k hik).2

/-- Every unordered pair contributes the common-superstring (optimum) row. -/
theorem unordered_pair {i j : Fin n} (hne : i ≠ j) :
    data.inputLength i + data.inputLength j ≤
      data.optimumLength + data.overlap i j + data.overlap j i := by
  exact GreedySuperstring.pair_in_common_superstring_of_reduced
    data.reduced (data.word_mem i) (data.word_mem j)
    (data.word_ne hne)
    (data.word_isInfix_common i) (data.word_isInfix_common j)
    (data.maximum i j hne).2
    (data.maximum j i (Ne.symm hne)).2

/-! Integral versions matching the signs of the dense LP rows. -/

theorem inputLength_nonnegative_int (i : Fin n) :
    (0 : ℤ) ≤ data.inputLength i := by
  exact_mod_cast data.inputLength_nonnegative i

theorem overlap_nonnegative_int (i j : Fin n) :
    (0 : ℤ) ≤ data.overlap i j := by
  exact_mod_cast data.overlap_nonnegative i j

theorem inputLength_le_optimumLength_int (i : Fin n) :
    (data.inputLength i : ℤ) ≤ data.optimumLength := by
  exact_mod_cast data.inputLength_le_optimumLength i

theorem overlap_le_source_int {i j : Fin n} (hne : i ≠ j) :
    (data.overlap i j : ℤ) ≤ data.inputLength i := by
  exact_mod_cast data.overlap_le_source hne

theorem overlap_le_target_int {i j : Fin n} (hne : i ≠ j) :
    (data.overlap i j : ℤ) ≤ data.inputLength j := by
  exact_mod_cast data.overlap_le_target hne

theorem directed_triangle_int {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (data.overlap i j : ℤ) + data.overlap j k ≤
      data.inputLength j + data.overlap i k := by
  exact_mod_cast data.directed_triangle hij hjk hik

/-- The pair row in its literal integral LP form. -/
theorem unordered_pair_int {i j : Fin n} (hne : i ≠ j) :
    (data.inputLength i : ℤ) + data.inputLength j -
        data.overlap i j - data.overlap j i ≤
      data.optimumLength := by
  have h := data.unordered_pair hne
  have h' :
      (data.inputLength i : ℤ) + data.inputLength j ≤
        data.optimumLength + data.overlap i j + data.overlap j i := by
    exact_mod_cast h
  omega

end WordInstance

/-- Sum the matrix weights along a nonempty directed label order. -/
def pathWeight {n : ℕ} (weight : Fin n → Fin n → ℕ)
    (head : Fin n) : List (Fin n) → ℕ
  | [] => 0
  | next :: rest => weight head next + pathWeight weight next rest

/-- A Hamiltonian ordering of all `Fin n` labels. Its head makes nonemptiness
explicit; consequently this type is uninhabited when `n = 0`. -/
structure HamiltonianOrder (n : ℕ) where
  head : Fin n
  rest : List (Fin n)
  perm : (head :: rest).Perm (List.ofFn id)

namespace HamiltonianOrder

variable {α : Type u} {n : ℕ}

theorem nodup (order : HamiltonianOrder n) :
    (order.head :: order.rest).Nodup := by
  apply order.perm.nodup_iff.mpr
  exact List.nodup_ofFn.mpr Function.injective_id

private def buildOverlapPath (data : WordInstance α n) :
    (head : Fin n) → (rest : List (Fin n)) →
      (head :: rest).Nodup →
      OverlapPath α (data.word head) (rest.map data.word)
  | head, [], _ => .nil (data.word head)
  | head, next :: remaining, hnodup =>
      have hparts := List.nodup_cons.mp hnodup
      have hne : head ≠ next := by
        intro heq
        subst next
        exact hparts.1 (by simp)
      .cons (data.overlap head next) (data.maximum head next hne).1
        (buildOverlapPath data next remaining hparts.2)

/-- The literal maximum-overlap path attached to a Hamiltonian label order. -/
def toOverlapPath (data : WordInstance α n) (order : HamiltonianOrder n) :
    OverlapPath α (data.word order.head) (order.rest.map data.word) :=
  buildOverlapPath data order.head order.rest order.nodup

/-- Matrix weight of the nominated Hamiltonian order. -/
def overlapWeight (data : WordInstance α n) (order : HamiltonianOrder n) : ℕ :=
  pathWeight data.overlap order.head order.rest

theorem toOverlapPath_overlapSum
    (data : WordInstance α n) (order : HamiltonianOrder n) :
    (order.toOverlapPath data).overlapSum = order.overlapWeight data := by
  have build_overlapSum :
      ∀ (head : Fin n) (rest : List (Fin n))
        (hnodup : (head :: rest).Nodup),
        (buildOverlapPath data head rest hnodup).overlapSum =
          pathWeight data.overlap head rest := by
    intro head rest hnodup
    induction rest generalizing head with
    | nil =>
        rfl
    | cons next remaining ih =>
        simp only [buildOverlapPath, pathWeight, OverlapPath.overlapSum,
          OverlapPath.overlapLengths_cons, List.sum_cons]
        exact congrArg (data.overlap head next + ·)
          (ih next (List.nodup_cons.mp hnodup).2)
  exact build_overlapSum order.head order.rest order.nodup

/-- A Hamiltonian order enumerates exactly the original words. -/
theorem words_perm (data : WordInstance α n) (order : HamiltonianOrder n) :
    (data.word order.head :: order.rest.map data.word).Perm
      (List.ofFn data.word) := by
  have hp := order.perm.map data.word
  simpa [List.map_ofFn, Function.comp_def] using hp

/-- The path's word-length sum is the data's total input length. -/
theorem totalWordLength_eq_totalInputLength
    (data : WordInstance α n) (order : HamiltonianOrder n) :
    OverlapPath.totalWordLength (data.word order.head)
        (order.rest.map data.word) = data.totalInputLength := by
  have hp := (order.words_perm data).map (fun word : Word α => word.length)
  have hsum := hp.sum_eq
  simpa [OverlapPath.totalWordLength, WordInstance.totalInputLength,
    WordInstance.inputLength, List.map_ofFn, Function.comp_def] using hsum

/-- Additive optimum-path normalization. The supplied equality says that
the literal maximum-overlap Hamiltonian path has exactly the common-word
length; `OverlapPath.length_add_overlapSum` then supplies the normalization
identity used by the LP. -/
theorem optimum_path_normalization_add
    (data : WordInstance α n) (order : HamiltonianOrder n)
    (hexact : (order.toOverlapPath data).superstring.length =
      data.optimumLength) :
    data.optimumLength + order.overlapWeight data =
      data.totalInputLength := by
  calc
    data.optimumLength + order.overlapWeight data =
        (order.toOverlapPath data).superstring.length +
          (order.toOverlapPath data).overlapSum := by
            rw [hexact, order.toOverlapPath_overlapSum data]
    _ = OverlapPath.totalWordLength (data.word order.head)
          (order.rest.map data.word) :=
      (order.toOverlapPath data).length_add_overlapSum
    _ = data.totalInputLength := order.totalWordLength_eq_totalInputLength data

/-- Subtractive Nat form of the nominated optimum-path equality. -/
theorem optimum_path_normalization
    (data : WordInstance α n) (order : HamiltonianOrder n)
    (hexact : (order.toOverlapPath data).superstring.length =
      data.optimumLength) :
    data.totalInputLength - order.overlapWeight data =
      data.optimumLength := by
  have h := order.optimum_path_normalization_add data hexact
  omega

/-- Integral LP form: sum of lengths minus nominated path weights is OPT. -/
theorem optimum_path_normalization_int
    (data : WordInstance α n) (order : HamiltonianOrder n)
    (hexact : (order.toOverlapPath data).superstring.length =
      data.optimumLength) :
    (data.totalInputLength : ℤ) - order.overlapWeight data =
      data.optimumLength := by
  have h := order.optimum_path_normalization_add data hexact
  have h' :
      (data.optimumLength : ℤ) + order.overlapWeight data =
        data.totalInputLength := by
    exact_mod_cast h
  omega

end HamiltonianOrder

end GreedySuperstring.Relaxation
