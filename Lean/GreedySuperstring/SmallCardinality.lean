import Lean.Elab.Tactic.Omega

/-!
# Arithmetic core for at most four inputs

This file formalizes Appendix A at the overlap/length level.  Every hypothesis
is a semantic inequality supplied by endpoint caps, greedy maximality, or a
directed overlap triangle; no finite enumeration is used.
-/

namespace GreedySuperstring.SmallCardinality

/-- Once the optimum path identity and the greedy saving inequality are
known, this is the common arithmetic finish used for four inputs. -/
theorem factorTwo_of_overlap_cover
    {total optimum greedy overlapSum saving : Nat}
    (optimalPath : optimum + overlapSum = total)
    (greedySaves : greedy + saving ≤ total)
    (cover : 2 * overlapSum ≤ total + saving) :
    greedy ≤ 2 * optimum := by
  omega

/-- The one-input case, where GREEDY and OPT are the same word. -/
theorem one_input {optimum greedy : Nat} (same : greedy = optimum) :
    greedy ≤ 2 * optimum := by
  omega

/-- Common two/three-input argument.  A Hamiltonian path has at most two
edges, each no heavier than the first greedy overlap `a`. -/
theorem two_or_three_inputs
    {total optimum greedy optimalOverlapSum a : Nat}
    (optimalPath : optimum + optimalOverlapSum = total)
    (optimalEdges : optimalOverlapSum ≤ 2 * a)
    (greedySaves : greedy + a ≤ total)
    (overlapAtMostOptimum : a ≤ optimum) :
    greedy ≤ 2 * optimum := by
  omega

/-- The sharper two-input specialization. -/
theorem two_inputs
    {total optimum greedy optimalOverlap a : Nat}
    (optimalPath : optimum + optimalOverlap = total)
    (optimalEdge : optimalOverlap ≤ a)
    (greedySaves : greedy + a ≤ total)
    (overlapAtMostOptimum : a ≤ optimum) :
    greedy ≤ 2 * optimum := by
  apply two_or_three_inputs optimalPath (by omega) greedySaves
    overlapAtMostOptimum

/-- Endpoint caps imply Appendix A inequality (A.1), in additive form:
`2(p+q+r) ≤ L + min(p,q) + min(q,r)`. -/
theorem endpoint_caps_A1
    {lengthA lengthB lengthC lengthD total p q r : Nat}
    (totalLength : total = lengthA + lengthB + lengthC + lengthD)
    (pAtA : p ≤ lengthA) (pAtB : p ≤ lengthB)
    (qAtB : q ≤ lengthB) (qAtC : q ≤ lengthC)
    (rAtC : r ≤ lengthC) (rAtD : r ≤ lengthD) :
    2 * (p + q + r) ≤ total + min p q + min q r := by
  rw [totalLength]
  rcases Nat.le_total p q with hpq | hqp
  · rcases Nat.le_total q r with hqr | hrq
    · simp [Nat.min_eq_left hpq, Nat.min_eq_left hqr]
      omega
    · simp [Nat.min_eq_left hpq, Nat.min_eq_right hrq]
      omega
  · rcases Nat.le_total q r with hqr | hrq
    · simp [Nat.min_eq_right hqp, Nat.min_eq_left hqr]
      omega
    · simp [Nat.min_eq_right hqp, Nat.min_eq_right hrq]
      omega

/-- `max(x,y)` plus `min(x,y)` can be charged to two lower bounds. -/
theorem min_add_min_le_of_regular_bounds
    {p q r a b : Nat}
    (first : max (min p q) (min q r) ≤ a)
    (second : min (min p q) (min q r) ≤ b) :
    min p q + min q r ≤ a + b := by
  let x := min p q
  let y := min q r
  rcases Nat.le_total x y with hxy | hyx
  · have hx : x ≤ b := by
      simpa [x, y, Nat.min_eq_left hxy] using second
    have hy : y ≤ a := by
      simpa [x, y, Nat.max_eq_right hxy] using first
    simpa [x, y, Nat.add_comm] using Nat.add_le_add hx hy
  · have hy : y ≤ b := by
      simpa [x, y, Nat.min_eq_right hyx] using second
    have hx : x ≤ a := by
      simpa [x, y, Nat.max_eq_left hyx] using first
    have := Nat.add_le_add hx hy
    simpa [x, y] using this

/-- The nonexceptional four-input branch from Appendix A. -/
theorem four_inputs_regular
    {lengthA lengthB lengthC lengthD total optimum greedy p q r a b : Nat}
    (totalLength : total = lengthA + lengthB + lengthC + lengthD)
    (optimalPath : optimum + (p + q + r) = total)
    (greedySaves : greedy + (a + b) ≤ total)
    (pAtA : p ≤ lengthA) (pAtB : p ≤ lengthB)
    (qAtB : q ≤ lengthB) (qAtC : q ≤ lengthC)
    (rAtC : r ≤ lengthC) (rAtD : r ≤ lengthD)
    (firstGreedy : max (min p q) (min q r) ≤ a)
    (secondGreedy : min (min p q) (min q r) ≤ b) :
    greedy ≤ 2 * optimum := by
  have endpoint := endpoint_caps_A1 totalLength pAtA pAtB qAtB qAtC
    rAtC rAtD
  have savings := min_add_min_le_of_regular_bounds firstGreedy secondGreedy
  apply factorTwo_of_overlap_cover optimalPath greedySaves
  omega

/-- Exact semantic premises for the reverse-middle exceptional branch.
`crossLeft` and `crossRight` are the still-feasible `A→C` and `B→D`
overlaps supplied by the two directed triangles. -/
def ReverseMiddleCase
    (lengthB lengthC p q r a b : Nat) : Prop :=
  ∃ crossLeft crossRight,
    p + q ≤ lengthB + crossLeft ∧
    q + r ≤ lengthC + crossRight ∧
    crossLeft ≤ a ∧ crossRight ≤ b


/-- The reverse-middle exceptional four-input branch. -/
theorem four_inputs_reverse_middle
    {lengthA lengthB lengthC lengthD total optimum greedy p q r a b : Nat}
    (totalLength : total = lengthA + lengthB + lengthC + lengthD)
    (optimalPath : optimum + (p + q + r) = total)
    (greedySaves : greedy + (a + b) ≤ total)
    (pAtA : p ≤ lengthA) (rAtD : r ≤ lengthD)
    (exceptional : ReverseMiddleCase lengthB lengthC p q r a b) :
    greedy ≤ 2 * optimum := by
  rcases exceptional with
    ⟨crossLeft, crossRight, leftTriangle, rightTriangle,
      leftFirst, rightSecond⟩
  have crossBound : crossLeft + crossRight ≤ a + b :=
    Nat.add_le_add leftFirst rightSecond
  have overlapCover :
      2 * (p + q + r) ≤ total + crossLeft + crossRight := by
    rw [totalLength]
    omega
  apply factorTwo_of_overlap_cover optimalPath greedySaves
  omega

/-- The two exhaustive semantic branches needed for the four-input proof. -/
def FourCase
    (lengthB lengthC p q r a b : Nat) : Prop :=
  (max (min p q) (min q r) ≤ a ∧
      min (min p q) (min q r) ≤ b) ∨
    ReverseMiddleCase lengthB lengthC p q r a b

/-- Appendix A's complete arithmetic conclusion.  The only combinatorial
input is `cases`: either an optimal edge survives the first merge and gives
the regular min/max bounds, or the selected edge is the reverse middle edge
and the two directed triangles give `ReverseMiddleCase`. -/
theorem four_inputs
    {lengthA lengthB lengthC lengthD total optimum greedy p q r a b : Nat}
    (totalLength : total = lengthA + lengthB + lengthC + lengthD)
    (optimalPath : optimum + (p + q + r) = total)
    (greedySaves : greedy + (a + b) ≤ total)
    (pAtA : p ≤ lengthA) (pAtB : p ≤ lengthB)
    (qAtB : q ≤ lengthB) (qAtC : q ≤ lengthC)
    (rAtC : r ≤ lengthC) (rAtD : r ≤ lengthD)
    (cases : FourCase lengthB lengthC p q r a b) :
    greedy ≤ 2 * optimum := by
  rcases cases with regular | exceptional
  · exact four_inputs_regular totalLength optimalPath greedySaves
      pAtA pAtB qAtB qAtC rAtC rAtD regular.1 regular.2
  · exact four_inputs_reverse_middle totalLength optimalPath greedySaves
      pAtA rAtD exceptional

end GreedySuperstring.SmallCardinality
