import Mathlib.Data.List.Infix
import Lean.Elab.Tactic.Omega

/-!
# Words, overlaps, and endpoint inheritance

This file contains the literal word-level kernel of the greedy-superstring
argument.  An overlap is represented relationally: `IsOverlap x y k` says
that the length-`k` suffix of `x` equals the length-`k` prefix of `y`.
Working relationally keeps every theorem independent of a particular
executable maximum-search implementation.
-/

namespace GreedySuperstring

abbrev Word (α : Type u) := List α

/-- `k` letters form a suffix-prefix overlap from `x` to `y`. -/
def IsOverlap (x y : Word α) (k : ℕ) : Prop :=
  k ≤ x.length ∧ k ≤ y.length ∧ x.drop (x.length - k) = y.take k

/-- Relational form of "every overlap from `x` to `y` has length at most `k`". -/
def OverlapLE (x y : Word α) (k : ℕ) : Prop :=
  ∀ r, IsOverlap x y r → r ≤ k

/-- `k` is a maximum suffix-prefix overlap from `x` to `y`. -/
def IsMaxOverlap (x y : Word α) (k : ℕ) : Prop :=
  IsOverlap x y k ∧ OverlapLE x y k

/-- Merge `x` into `y` at a certified overlap of length `k`. -/
def mergeAt (x y : Word α) (k : ℕ) : Word α :=
  x ++ y.drop k

/-- A list of words is reduced: it has no duplicates, and no distinct member
is a contiguous subword of another member. -/
def Reduced (S : List (Word α)) : Prop :=
  S.Nodup ∧ ∀ ⦃x y⦄, x ∈ S → y ∈ S → x ≠ y → ¬x.IsInfix y

/-- `k` is globally maximal among overlaps between distinct members of `S`. -/
def GloballyMaximal (S : List (Word α)) (k : ℕ) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x ≠ y → OverlapLE x y k

theorem overlap_zero (x y : Word α) : IsOverlap x y 0 := by
  simp [IsOverlap]

theorem overlap_left_bound {x y : Word α} {k : ℕ}
    (h : IsOverlap x y k) : k ≤ x.length := h.1

theorem overlap_right_bound {x y : Word α} {k : ℕ}
    (h : IsOverlap x y k) : k ≤ y.length := h.2.1

theorem mergeAt_length {x y : Word α} {k : ℕ} (hk : k ≤ y.length) :
    (mergeAt x y k).length = x.length + y.length - k := by
  simp [mergeAt, List.length_drop]
  omega

theorem left_isPrefix_mergeAt (x y : Word α) (k : ℕ) :
    x.IsPrefix (mergeAt x y k) := by
  exact ⟨y.drop k, rfl⟩

theorem left_isInfix_mergeAt (x y : Word α) (k : ℕ) :
    x.IsInfix (mergeAt x y k) :=
  (left_isPrefix_mergeAt x y k).isInfix

theorem right_isSuffix_mergeAt {x y : Word α} {k : ℕ}
    (h : IsOverlap x y k) : y.IsSuffix (mergeAt x y k) := by
  refine ⟨x.take (x.length - k), ?_⟩
  calc
    x.take (x.length - k) ++ y =
        x.take (x.length - k) ++ (y.take k ++ y.drop k) := by
          rw [y.take_append_drop k]
    _ = (x.take (x.length - k) ++ y.take k) ++ y.drop k := by
          rw [List.append_assoc]
    _ = (x.take (x.length - k) ++ x.drop (x.length - k)) ++ y.drop k := by
          rw [h.2.2]
    _ = x ++ y.drop k := by
          rw [x.take_append_drop (x.length - k)]
    _ = mergeAt x y k := rfl

theorem right_isInfix_mergeAt {x y : Word α} {k : ℕ}
    (h : IsOverlap x y k) : y.IsInfix (mergeAt x y k) :=
  (right_isSuffix_mergeAt h).isInfix

theorem maxOverlap_unique {x y : Word α} {k r : ℕ}
    (hk : IsMaxOverlap x y k) (hr : IsMaxOverlap x y r) : k = r := by
  apply Nat.le_antisymm
  · exact hr.2 k hk.1
  · exact hk.2 r hr.1

/-- On a reduced family, an overlap between distinct members is proper at the
right endpoint. -/
theorem overlap_lt_right_of_reduced {S : List (Word α)} {x y : Word α} {k : ℕ}
    (hred : Reduced S) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hov : IsOverlap x y k) : k < y.length := by
  apply Nat.lt_of_le_of_ne hov.2.1
  intro hk
  have hdrop : x.drop (x.length - k) = y := by
    rw [hov.2.2, hk, y.take_length]
  have hsuf : y.IsSuffix x := ⟨x.take (x.length - k), by
    rw [← hdrop, x.take_append_drop (x.length - k)]⟩
  exact hred.2 hy hx (Ne.symm hne) hsuf.isInfix

/-- On a reduced family, an overlap between distinct members is proper at the
left endpoint. -/
theorem overlap_lt_left_of_reduced {S : List (Word α)} {x y : Word α} {k : ℕ}
    (hred : Reduced S) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hov : IsOverlap x y k) : k < x.length := by
  apply Nat.lt_of_le_of_ne hov.1
  intro hk
  have hxy : x = y.take k := by
    simpa [hk] using hov.2.2
  have hpref : x.IsPrefix y := by
    refine ⟨y.drop k, ?_⟩
    rw [hxy, y.take_append_drop k]
  exact hred.2 hx hy hne hpref.isInfix

private theorem take_eq_of_isPrefix {x m : List α} {r : ℕ}
    (h : x.IsPrefix m) (hr : r ≤ x.length) : m.take r = x.take r := by
  rcases h with ⟨p, rfl⟩
  exact List.take_append_of_le_length hr

private theorem drop_eq_of_isSuffix {y m : List α} {r : ℕ}
    (h : y.IsSuffix m) (hr : r ≤ y.length) :
    m.drop (m.length - r) = y.drop (y.length - r) := by
  rcases h with ⟨p, rfl⟩
  rw [List.length_append, List.drop_append]
  have hp : p.length ≤ p.length + y.length - r := by omega
  rw [List.drop_eq_nil_of_le hp]
  have harith : p.length + y.length - r - p.length = y.length - r := by omega
  rw [harith]
  rfl

/-- Every overlap no longer than the inherited right endpoint is preserved. -/
theorem isOverlap_mergeAt_right_iff {a b z : Word α} {k r : ℕ}
    (hab : IsOverlap a b k) (hr : r ≤ b.length) :
    IsOverlap (mergeAt a b k) z r ↔ IsOverlap b z r := by
  have hb : b.IsSuffix (mergeAt a b k) := right_isSuffix_mergeAt hab
  constructor
  · intro h
    refine ⟨hr, h.2.1, ?_⟩
    calc
      b.drop (b.length - r) =
          (mergeAt a b k).drop ((mergeAt a b k).length - r) :=
        (drop_eq_of_isSuffix hb hr).symm
      _ = z.take r := h.2.2
  · intro h
    refine ⟨?_, h.2.1, ?_⟩
    · have hlen := hb.length_le
      omega
    · calc
        (mergeAt a b k).drop ((mergeAt a b k).length - r) =
            b.drop (b.length - r) := drop_eq_of_isSuffix hb hr
        _ = z.take r := h.2.2

/-- Every overlap no longer than the inherited left endpoint is preserved. -/
theorem isOverlap_mergeAt_left_iff {z a b : Word α} {k r : ℕ}
    (hr : r ≤ a.length) :
    IsOverlap z (mergeAt a b k) r ↔ IsOverlap z a r := by
  have ha : a.IsPrefix (mergeAt a b k) := left_isPrefix_mergeAt a b k
  constructor
  · intro h
    refine ⟨h.1, hr, ?_⟩
    calc
      z.drop (z.length - r) = (mergeAt a b k).take r := h.2.2
      _ = a.take r := take_eq_of_isPrefix ha hr
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · have hlen := ha.length_le
      omega
    · calc
        z.drop (z.length - r) = a.take r := h.2.2
        _ = (mergeAt a b k).take r := (take_eq_of_isPrefix ha hr).symm

/-- A crossing overlap leaving a merge induces a longer overlap from the left
constituent.  This is the key contradiction used by outgoing inheritance. -/
theorem crossing_right_overlap {a b z : Word α} {k r : ℕ}
    (hab : IsOverlap a b k)
    (hmz : IsOverlap (mergeAt a b k) z r)
    (hr : b.length < r) :
    IsOverlap a z (r - b.length + k) := by
  let q := r - b.length + k
  have hk_b : k ≤ b.length := hab.2.1
  have hm_len : (mergeAt a b k).length = a.length + b.length - k :=
    mergeAt_length hk_b
  have hq_a : q ≤ a.length := by
    have hr_m := hmz.1
    rw [hm_len] at hr_m
    dsimp [q]
    omega
  have hq_r : q ≤ r := by
    dsimp [q]
    omega
  have hq_z : q ≤ z.length := Nat.le_trans hq_r hmz.2.1
  refine ⟨hq_a, hq_z, ?_⟩
  have hstart : (mergeAt a b k).length - r = a.length - q := by
    dsimp [q]
    rw [hm_len]
    omega
  have hdrop_len : (a.drop (a.length - q)).length = q := by
    rw [List.length_drop]
    omega
  have htake_merge :
      ((mergeAt a b k).drop (a.length - q)).take q =
        a.drop (a.length - q) := by
    rw [mergeAt, List.drop_append_of_le_length (Nat.sub_le _ _)]
    rw [List.take_append_of_le_length (Nat.le_of_eq hdrop_len.symm)]
    exact List.take_of_length_le (Nat.le_of_eq hdrop_len)
  calc
    a.drop (a.length - q) =
        ((mergeAt a b k).drop (a.length - q)).take q := htake_merge.symm
    _ = (z.take r).take q := by rw [← hstart, hmz.2.2]
    _ = z.take q := by
      rw [List.take_take]
      simp [Nat.min_eq_left hq_r]

private theorem drop_mergeAt_overlap {a b : Word α} {k : ℕ}
    (hab : IsOverlap a b k) :
    (mergeAt a b k).drop (a.length - k) = b := by
  rw [mergeAt, List.drop_append_of_le_length (Nat.sub_le _ _)]
  rw [hab.2.2, b.take_append_drop k]

/-- A crossing overlap entering a merge induces a longer overlap into the
right constituent.  This is the key contradiction used by incoming
inheritance. -/
theorem crossing_left_overlap {z a b : Word α} {k r : ℕ}
    (hab : IsOverlap a b k)
    (hzm : IsOverlap z (mergeAt a b k) r)
    (hr : a.length < r) :
    IsOverlap z b (r - a.length + k) := by
  let q := r - a.length + k
  have hk_a : k ≤ a.length := hab.1
  have hk_b : k ≤ b.length := hab.2.1
  have hm_len : (mergeAt a b k).length = a.length + b.length - k :=
    mergeAt_length hk_b
  have hq_b : q ≤ b.length := by
    have hr_m := hzm.2.1
    rw [hm_len] at hr_m
    dsimp [q]
    omega
  have hq_r : q ≤ r := by
    dsimp [q]
    omega
  have hq_z : q ≤ z.length := Nat.le_trans hq_r hzm.1
  refine ⟨hq_z, hq_b, ?_⟩
  have hdelta : r - q = a.length - k := by
    dsimp [q]
    omega
  have hsum : z.length - r + (r - q) = z.length - q :=
    Nat.sub_add_sub_cancel hzm.1 hq_r
  calc
    z.drop (z.length - q) =
        (z.drop (z.length - r)).drop (r - q) := by
          rw [List.drop_drop, hsum]
    _ = ((mergeAt a b k).take r).drop (r - q) := by
          rw [hzm.2.2]
    _ = ((mergeAt a b k).drop (r - q)).take (r - (r - q)) := by
          rw [List.drop_take]
    _ = ((mergeAt a b k).drop (a.length - k)).take q := by
          rw [Nat.sub_sub_self hq_r, hdelta]
    _ = b.take q := by rw [drop_mergeAt_overlap hab]

/-- Exact inheritance of the outgoing overlap interface.  Global maximality
is used only through the local bound `OverlapLE a z k`. -/
theorem right_overlap_interface {a b z : Word α} {k r : ℕ}
    (hab : IsOverlap a b k) (haz : OverlapLE a z k) :
    IsOverlap (mergeAt a b k) z r ↔ IsOverlap b z r := by
  constructor
  · intro h
    have hr_b : r ≤ b.length := by
      apply Nat.le_of_not_gt
      intro hr
      have hcross : IsOverlap a z (r - b.length + k) :=
        crossing_right_overlap hab h hr
      have hle := haz _ hcross
      omega
    exact (isOverlap_mergeAt_right_iff hab hr_b).mp h
  · intro h
    exact (isOverlap_mergeAt_right_iff hab h.1).mpr h

/-- Exact inheritance of the incoming overlap interface.  Global maximality
is used only through the local bound `OverlapLE z b k`. -/
theorem left_overlap_interface {z a b : Word α} {k r : ℕ}
    (hab : IsOverlap a b k) (hzb : OverlapLE z b k) :
    IsOverlap z (mergeAt a b k) r ↔ IsOverlap z a r := by
  constructor
  · intro h
    have hr_a : r ≤ a.length := by
      apply Nat.le_of_not_gt
      intro hr
      have hcross : IsOverlap z b (r - a.length + k) :=
        crossing_left_overlap hab h hr
      have hle := hzb _ hcross
      omega
    exact (isOverlap_mergeAt_left_iff hr_a).mp h
  · intro h
    exact (isOverlap_mergeAt_left_iff h.2.1).mpr h

theorem right_maxOverlap_interface {a b z : Word α} {k r : ℕ}
    (hab : IsOverlap a b k) (haz : OverlapLE a z k) :
    IsMaxOverlap (mergeAt a b k) z r ↔ IsMaxOverlap b z r := by
  constructor
  · intro h
    refine ⟨(right_overlap_interface hab haz).mp h.1, ?_⟩
    intro q hq
    exact h.2 q ((right_overlap_interface hab haz).mpr hq)
  · intro h
    refine ⟨(right_overlap_interface hab haz).mpr h.1, ?_⟩
    intro q hq
    exact h.2 q ((right_overlap_interface hab haz).mp hq)

theorem left_maxOverlap_interface {z a b : Word α} {k r : ℕ}
    (hab : IsOverlap a b k) (hzb : OverlapLE z b k) :
    IsMaxOverlap z (mergeAt a b k) r ↔ IsMaxOverlap z a r := by
  constructor
  · intro h
    refine ⟨(left_overlap_interface hab hzb).mp h.1, ?_⟩
    intro q hq
    exact h.2 q ((left_overlap_interface hab hzb).mpr hq)
  · intro h
    refine ⟨(left_overlap_interface hab hzb).mpr h.1, ?_⟩
    intro q hq
    exact h.2 q ((left_overlap_interface hab hzb).mp hq)

/-- Outgoing endpoint inheritance in the form used by a globally maximal
greedy merge. -/
theorem right_overlap_interface_of_global {S : List (Word α)} {a b z : Word α}
    {k r : ℕ} (hab : IsOverlap a b k) (hglobal : GloballyMaximal S k)
    (ha : a ∈ S) (hz : z ∈ S) (haz : a ≠ z) :
    IsOverlap (mergeAt a b k) z r ↔ IsOverlap b z r :=
  right_overlap_interface hab (hglobal ha hz haz)

/-- Incoming endpoint inheritance in the form used by a globally maximal
greedy merge. -/
theorem left_overlap_interface_of_global {S : List (Word α)} {z a b : Word α}
    {k r : ℕ} (hab : IsOverlap a b k) (hglobal : GloballyMaximal S k)
    (hz : z ∈ S) (hb : b ∈ S) (hzb : z ≠ b) :
    IsOverlap z (mergeAt a b k) r ↔ IsOverlap z a r :=
  left_overlap_interface hab (hglobal hz hb hzb)

/-- The literal intersection behind the directed overlap triangle.  Overlaps
of lengths `p : a → b` and `q : b → c` induce an `a → c` overlap of length
`p + q - |b|`. -/
theorem overlap_triangle_witness {a b c : Word α} {p q : ℕ}
    (hab : IsOverlap a b p) (hbc : IsOverlap b c q) :
    IsOverlap a c (p + q - b.length) := by
  let r := p + q - b.length
  by_cases hpq : p + q ≤ b.length
  · simpa [Nat.sub_eq_zero_of_le hpq] using overlap_zero a c
  · have hp_b : p ≤ b.length := hab.2.1
    have hq_b : q ≤ b.length := hbc.1
    have hr_p : r ≤ p := by
      dsimp [r]
      omega
    have hr_q : r ≤ q := by
      dsimp [r]
      omega
    have hr_a : r ≤ a.length := Nat.le_trans hr_p hab.1
    have hr_c : r ≤ c.length := Nat.le_trans hr_q hbc.2.1
    refine ⟨hr_a, hr_c, ?_⟩
    have hsum : a.length - p + (p - r) = a.length - r :=
      Nat.sub_add_sub_cancel hab.1 hr_p
    have hdelta : p - r = b.length - q := by
      dsimp [r]
      omega
    calc
      a.drop (a.length - r) =
          (a.drop (a.length - p)).drop (p - r) := by
            rw [List.drop_drop, hsum]
      _ = (b.take p).drop (p - r) := by rw [hab.2.2]
      _ = (b.drop (p - r)).take (p - (p - r)) := by
            rw [List.drop_take]
      _ = (b.drop (b.length - q)).take r := by
            rw [Nat.sub_sub_self hr_p, hdelta]
      _ = (c.take q).take r := by rw [hbc.2.2]
      _ = c.take r := by
            rw [List.take_take]
            simp [Nat.min_eq_left hr_q]

/-- Directed overlap triangle in inequality form. -/
theorem directed_overlap_triangle {a b c : Word α} {p q r : ℕ}
    (hab : IsOverlap a b p) (hbc : IsOverlap b c q)
    (hac : OverlapLE a c r) :
    p + q ≤ b.length + r := by
  have hle := hac _ (overlap_triangle_witness hab hbc)
  omega

end GreedySuperstring

namespace GreedySuperstring

private theorem infix_of_occurrence_inside_prefix
    {p z t a m : List α} (hocc : p ++ z ++ t = m)
    (ha : a.IsPrefix m) (hend : p.length + z.length ≤ a.length) :
    z.IsInfix a := by
  have hpz : (p ++ z).IsPrefix m := by
    refine ⟨t, ?_⟩
    simpa [List.append_assoc] using hocc
  have hpztake := hpz.take a.length
  have hpzlen : (p ++ z).length ≤ a.length := by simpa using hend
  rw [List.take_of_length_le hpzlen] at hpztake
  have htake : m.take a.length = a := by
    rcases ha with ⟨u, rfl⟩
    simp
  rw [htake] at hpztake
  exact (List.suffix_append p z).isInfix.trans hpztake.isInfix

private theorem infix_of_occurrence_inside_suffix
    {p z t b m : List α} (hocc : p ++ z ++ t = m)
    (hb : b.IsSuffix m) (hstart : m.length - b.length ≤ p.length) :
    z.IsInfix b := by
  let d := m.length - b.length
  have hdrop : m.drop d = b := by
    rcases hb with ⟨u, hu⟩
    have hd : d = u.length := by
      dsimp [d]
      rw [← hu]
      simp
    rw [hd, ← hu]
    simp
  refine ⟨p.drop d, t, ?_⟩
  have hdle : d ≤ p.length := by simpa [d] using hstart
  calc
    p.drop d ++ z ++ t = p.drop d ++ (z ++ t) := by simp [List.append_assoc]
    _ = (p ++ (z ++ t)).drop d := (List.drop_append_of_le_length hdle).symm
    _ = (p ++ z ++ t).drop d := by simp [List.append_assoc]
    _ = m.drop d := by rw [hocc]
    _ = b := hdrop

/-- If an old word occurs across the junction of a proper merge, its prefix
through the end of `a` is an overlap from `a` longer than `k`. -/
theorem crossing_infix_overlap {p z t a b : Word α} {k : ℕ}
    (hab : IsOverlap a b k)
    (hocc : p ++ z ++ t = mergeAt a b k)
    (hna : ¬z.IsInfix a) (hnb : ¬z.IsInfix b) :
    ∃ q, k < q ∧ IsOverlap a z q := by
  have ha : a.IsPrefix (mergeAt a b k) := left_isPrefix_mergeAt a b k
  have hb : b.IsSuffix (mergeAt a b k) := right_isSuffix_mergeAt hab
  have hend : a.length < p.length + z.length := by
    apply Nat.lt_of_not_ge
    intro hle
    exact hna (infix_of_occurrence_inside_prefix hocc ha hle)
  have hstart : p.length < (mergeAt a b k).length - b.length := by
    apply Nat.lt_of_not_ge
    intro hle
    exact hnb (infix_of_occurrence_inside_suffix hocc hb hle)
  let q := a.length - p.length
  have hm_len : (mergeAt a b k).length = a.length + b.length - k :=
    mergeAt_length hab.2.1
  have hstart' : p.length < a.length - k := by
    rw [hm_len] at hstart
    omega
  have hkq : k < q := by
    dsimp [q]
    omega
  have hqz : q ≤ z.length := by
    dsimp [q]
    omega
  refine ⟨q, hkq, Nat.sub_le _ _, hqz, ?_⟩
  have htake : (mergeAt a b k).take a.length = a := by
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    simp
  have hdrop_p : (p ++ z ++ t).drop p.length = z ++ t := by
    calc
      (p ++ z ++ t).drop p.length = (p ++ (z ++ t)).drop p.length := by
        simp [List.append_assoc]
      _ = p.drop p.length ++ (z ++ t) :=
        List.drop_append_of_le_length (le_refl p.length)
      _ = z ++ t := by simp
  calc
    a.drop (a.length - q) = a.drop p.length := by
      congr 1
      dsimp [q]
      omega
    _ = ((mergeAt a b k).take a.length).drop p.length := by rw [htake]
    _ = ((p ++ z ++ t).take a.length).drop p.length := by rw [hocc]
    _ = ((p ++ z ++ t).drop p.length).take (a.length - p.length) := by
      rw [List.drop_take]
    _ = (z ++ t).take (a.length - p.length) := by rw [hdrop_p]
    _ = (z ++ t).take q := rfl
    _ = z.take q := List.take_append_of_le_length hqz

/-- Every surviving old word is incomparable by substring with a globally
maximal merge. -/
theorem old_word_incomparable_with_global_merge
    {S : List (Word α)} {a b z : Word α} {k : ℕ}
    (hred : Reduced S) (hab : IsOverlap a b k)
    (hglobal : GloballyMaximal S k)
    (ha : a ∈ S) (hb : b ∈ S) (hz : z ∈ S)
    (hza : z ≠ a) (hzb : z ≠ b) :
    ¬(mergeAt a b k).IsInfix z ∧ ¬z.IsInfix (mergeAt a b k) := by
  constructor
  · intro hmz
    exact hred.2 ha hz (Ne.symm hza) ((left_isInfix_mergeAt a b k).trans hmz)
  · intro hzm
    rcases hzm with ⟨p, t, hocc⟩
    have hna : ¬z.IsInfix a := hred.2 hz ha hza
    have hnb : ¬z.IsInfix b := hred.2 hz hb hzb
    rcases crossing_infix_overlap hab hocc hna hnb with ⟨q, hkq, hq⟩
    have hle := hglobal ha hz (Ne.symm hza) q hq
    omega

/-- Predicate describing the members that remain after replacing `a,b` by
their merge. -/
def AfterMerge (S : List (Word α)) (a b : Word α) (k : ℕ) (x : Word α) : Prop :=
  x = mergeAt a b k ∨ (x ∈ S ∧ x ≠ a ∧ x ≠ b)

/-- A globally maximal merge preserves the substring-antichain property. -/
theorem globallyMaximal_merge_preserves_antichain
    {S : List (Word α)} {a b : Word α} {k : ℕ}
    (hred : Reduced S) (hab : IsOverlap a b k)
    (hglobal : GloballyMaximal S k) (ha : a ∈ S) (hb : b ∈ S) :
    ∀ ⦃x y⦄, AfterMerge S a b k x → AfterMerge S a b k y →
      x ≠ y → ¬x.IsInfix y := by
  intro x y hx hy hxy
  rcases hx with rfl | ⟨hxS, hxa, hxb⟩
  · rcases hy with rfl | ⟨hyS, hya, hyb⟩
    · exact (hxy rfl).elim
    · exact (old_word_incomparable_with_global_merge hred hab hglobal
        ha hb hyS hya hyb).1
  · rcases hy with rfl | ⟨hyS, hya, hyb⟩
    · exact (old_word_incomparable_with_global_merge hred hab hglobal
        ha hb hxS hxa hxb).2
    · exact hred.2 hxS hyS hxy

end GreedySuperstring

namespace GreedySuperstring

/-- The literal intersection behind the conditional directed rectangle.
If `a : u → v`, `x : u → c`, and `z : d → v` are overlap lengths with
`x ≤ a` and `z ≤ a`, then `d → c` has an overlap of length `x + z - a`. -/
theorem overlap_rectangle_witness {u v c d : Word α} {a x z : ℕ}
    (huv : IsOverlap u v a) (huc : IsOverlap u c x)
    (hdv : IsOverlap d v z) (hxa : x ≤ a) (hza : z ≤ a) :
    IsOverlap d c (x + z - a) := by
  let r := x + z - a
  by_cases hxz : x + z ≤ a
  · simpa [Nat.sub_eq_zero_of_le hxz] using overlap_zero d c
  · have hrx : r ≤ x := by
      dsimp [r]
      omega
    have hrz : r ≤ z := by
      dsimp [r]
      omega
    have hrd : r ≤ d.length := Nat.le_trans hrz hdv.1
    have hrc : r ≤ c.length := Nat.le_trans hrx huc.2.1
    refine ⟨hrd, hrc, ?_⟩
    have hdu : d.length - z + (z - r) = d.length - r :=
      Nat.sub_add_sub_cancel hdv.1 hrz
    have hzdelta : z - r = a - x := by
      dsimp [r]
      omega
    have hux : u.length - a + (a - x) = u.length - x :=
      Nat.sub_add_sub_cancel huv.1 hxa
    have hsegment : (v.drop (a - x)).take x = c.take x := by
      calc
        (v.drop (a - x)).take x = (v.take a).drop (a - x) := by
          rw [List.drop_take, Nat.sub_sub_self hxa]
        _ = (u.drop (u.length - a)).drop (a - x) := by rw [huv.2.2]
        _ = u.drop (u.length - x) := by rw [List.drop_drop, hux]
        _ = c.take x := huc.2.2
    calc
      d.drop (d.length - r) =
          (d.drop (d.length - z)).drop (z - r) := by
            rw [List.drop_drop, hdu]
      _ = (v.take z).drop (z - r) := by rw [hdv.2.2]
      _ = (v.drop (z - r)).take (z - (z - r)) := by
            rw [List.drop_take]
      _ = (v.drop (a - x)).take r := by
            rw [Nat.sub_sub_self hrz, hzdelta]
      _ = ((v.drop (a - x)).take x).take r := by
            rw [List.take_take]
            simp [Nat.min_eq_left hrx]
      _ = (c.take x).take r := by rw [hsegment]
      _ = c.take r := by
            rw [List.take_take]
            simp [Nat.min_eq_left hrx]

/-- Conditional directed rectangle in inequality form. -/
theorem conditional_directed_rectangle {u v c d : Word α} {a x z w : ℕ}
    (huv : IsOverlap u v a) (huc : IsOverlap u c x)
    (hdv : IsOverlap d v z) (hxa : x ≤ a) (hza : z ≤ a)
    (hdc : OverlapLE d c w) :
    x + z ≤ a + w := by
  have hle := hdc _ (overlap_rectangle_witness huv huc hdv hxa hza)
  omega

end GreedySuperstring

namespace GreedySuperstring

private theorem occurrence_prefix_after_start
    {p x s t : List α} (hocc : p ++ x ++ s = t) :
    x.IsPrefix (t.drop p.length) := by
  refine ⟨s, ?_⟩
  rw [← hocc]
  simp [List.append_assoc]

private theorem occurrence_remainder_prefix_at_later_start
    {p x s t : List α} {q : List β}
    (hocc : p ++ x ++ s = t) (hstart : p.length ≤ q.length) :
    (x.drop (q.length - p.length)).IsPrefix (t.drop q.length) := by
  have hp : (p ++ x).IsPrefix t := ⟨s, hocc⟩
  have hd := hp.drop q.length
  have heq : (p ++ x).drop q.length = x.drop (q.length - p.length) := by
    rw [List.drop_append, List.drop_eq_nil_of_le hstart]
    simp
  rw [heq] at hd
  exact hd

private theorem prefix_of_common_prefix {x y t : List α}
    (hx : x.IsPrefix t) (hy : y.IsPrefix t) (hlen : x.length ≤ y.length) :
    x.IsPrefix y := by
  rw [List.prefix_iff_eq_take] at hx hy ⊢
  calc
    x = t.take x.length := hx
    _ = (t.take y.length).take x.length := by
      rw [List.take_take]
      simp [Nat.min_eq_left hlen]
    _ = y.take x.length := (congrArg (List.take x.length) hy).symm

/-- If two chosen occurrences are ordered by both start and end, their
geometric intersection is a directed suffix-prefix overlap. -/
theorem ordered_occurrences_overlap_witness
    {pi i si pj j sj t : Word α}
    (hi : pi ++ i ++ si = t) (hj : pj ++ j ++ sj = t)
    (hstart : pi.length ≤ pj.length)
    (hend : pi.length + i.length ≤ pj.length + j.length) :
    IsOverlap i j (i.length - (pj.length - pi.length)) := by
  let d := pj.length - pi.length
  let r := i.length - d
  by_cases hdisjoint : i.length ≤ d
  · have hzero : i.length - (pj.length - pi.length) = 0 := by
      apply Nat.sub_eq_zero_of_le
      simpa [d] using hdisjoint
    simpa [hzero] using overlap_zero i j
  · have hd_i : d ≤ i.length := Nat.le_of_lt (Nat.lt_of_not_ge hdisjoint)
    have hr_i : r ≤ i.length := Nat.sub_le _ _
    have hr_j : r ≤ j.length := by
      dsimp [r, d]
      omega
    refine ⟨hr_i, hr_j, ?_⟩
    have hiTail : (i.drop d).IsPrefix (t.drop pj.length) :=
      occurrence_remainder_prefix_at_later_start hi hstart
    have hjTail : j.IsPrefix (t.drop pj.length) :=
      occurrence_prefix_after_start hj
    have hdrop_len : (i.drop d).length = r := by
      simp [r]
    have hiPrefixJ : (i.drop d).IsPrefix j :=
      prefix_of_common_prefix hiTail hjTail (by simpa [hdrop_len] using hr_j)
    have hiEq : i.drop d = j.take r := by
      rw [List.prefix_iff_eq_take] at hiPrefixJ
      simpa [hdrop_len] using hiPrefixJ
    calc
      i.drop (i.length - r) = i.drop d := by
        dsimp [r]
        rw [Nat.sub_sub_self hd_i]
      _ = j.take r := hiEq

/-- The directional occurrence lemma used by the pair inequality.  If the
second occurrence starts later and is not nested in the first word, it
constructs an overlap and the corresponding length bound. -/
theorem directional_occurrence_overlap
    {pi i si pj j sj t : Word α}
    (hi : pi ++ i ++ si = t) (hj : pj ++ j ++ sj = t)
    (hstart : pi.length ≤ pj.length) (hnot : ¬j.IsInfix i) :
    ∃ r, IsOverlap i j r ∧ i.length + j.length ≤ t.length + r := by
  have hend : pi.length + i.length ≤ pj.length + j.length := by
    apply Nat.le_of_not_gt
    intro hnend
    let d := pj.length - pi.length
    have hiTail : (i.drop d).IsPrefix (t.drop pj.length) :=
      occurrence_remainder_prefix_at_later_start hi hstart
    have hjTail : j.IsPrefix (t.drop pj.length) :=
      occurrence_prefix_after_start hj
    have hjlen : j.length ≤ (i.drop d).length := by
      simp [d]
      omega
    have hjPrefix : j.IsPrefix (i.drop d) :=
      prefix_of_common_prefix hjTail hiTail hjlen
    exact hnot (hjPrefix.isInfix.trans (List.drop_suffix d i).isInfix)
  let r := i.length - (pj.length - pi.length)
  have hov : IsOverlap i j r := ordered_occurrences_overlap_witness hi hj hstart hend
  have ht : pj.length + j.length + sj.length = t.length := by
    simpa [Nat.add_assoc] using congrArg List.length hj
  refine ⟨r, hov, ?_⟩
  dsimp [r]
  omega

/-- Pair-in-a-common-superstring inequality for substring-incomparable words.
The incomparability hypotheses are necessary: the unrestricted statement is
false when one word occurs strictly inside the other. -/
theorem pair_in_common_superstring
    {i j t : Word α} {wij wji : ℕ}
    (hi : i.IsInfix t) (hj : j.IsInfix t)
    (hij : ¬i.IsInfix j) (hji : ¬j.IsInfix i)
    (hijLE : OverlapLE i j wij) (hjiLE : OverlapLE j i wji) :
    i.length + j.length ≤ t.length + wij + wji := by
  rcases hi with ⟨pi, si, hi⟩
  rcases hj with ⟨pj, sj, hj⟩
  rcases Nat.le_total pi.length pj.length with hstart | hstart
  · rcases directional_occurrence_overlap hi hj hstart hji with ⟨r, hr, hlen⟩
    have hrle := hijLE r hr
    omega
  · rcases directional_occurrence_overlap hj hi hstart hij with ⟨r, hr, hlen⟩
    have hrle := hjiLE r hr
    omega

/-- Reduced-family form of `pair_in_common_superstring`. -/
theorem pair_in_common_superstring_of_reduced
    {S : List (Word α)} {i j t : Word α} {wij wji : ℕ}
    (hred : Reduced S) (hiS : i ∈ S) (hjS : j ∈ S) (hne : i ≠ j)
    (hi : i.IsInfix t) (hj : j.IsInfix t)
    (hijLE : OverlapLE i j wij) (hjiLE : OverlapLE j i wji) :
    i.length + j.length ≤ t.length + wij + wji :=
  pair_in_common_superstring hi hj
    (hred.2 hiS hjS hne) (hred.2 hjS hiS (Ne.symm hne)) hijLE hjiLE

end GreedySuperstring
