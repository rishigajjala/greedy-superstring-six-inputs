import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact scaled dual certificates

This file is the small mathematical kernel used by the finite certificate
checker. It proves weak duality for the homogeneous integer LP used in the
computer-assisted proof. Certificate conversion may be untrusted: a
certificate is useful only after Lean has checked every condition below.
-/

namespace GreedySuperstring.LP

open scoped BigOperators

variable {ρ ν : Type*} [Fintype ρ] [DecidableEq ρ]
  [Fintype ν] [DecidableEq ν]

/-- Dot product of two integer vectors over a finite coordinate type. -/
def dot (a x : ν → ℤ) : ℤ := ∑ v, a v * x v

/-- Deterministic homogeneous primal model.

The right-hand side is the coefficient of the optimum value O in a row.
Only coordinates in bounded have the finite upper bound x v ≤ O.
-/
structure Model (ρ ν : Type*) [Fintype ρ] [Fintype ν]
    [DecidableEq ν] where
  row : ρ → ν → ℤ
  rhs : ρ → ℤ
  equality : ν → ℤ
  objective : ν → ℤ
  bounded : Finset ν

/-- A primal point for optimum parameter O. -/
structure Primal (M : Model ρ ν) (O : ℤ) where
  x : ν → ℤ
  opt_nonneg : 0 ≤ O
  nonneg : ∀ v, 0 ≤ x v
  rows : ∀ r, dot (M.row r) x ≤ M.rhs r * O
  equality : dot M.equality x = O
  upper : ∀ v ∈ M.bounded, x v ≤ O

/-- A denominator-cleared exact dual certificate.

Scale is the common positive denominator. Inequality multipliers are
nonpositive because primal rows have the form A x ≤ b O; lower-bound
multipliers are nonnegative; and upper-bound multipliers are nonpositive.
-/
structure ScaledDual (M : Model ρ ν) where
  scale : ℤ
  y : ρ → ℤ
  z : ℤ
  lower : ν → ℤ
  upper : ν → ℤ
  scale_pos : 0 < scale
  y_nonpos : ∀ r, y r ≤ 0
  lower_nonneg : ∀ v, 0 ≤ lower v
  upper_nonpos : ∀ v, upper v ≤ 0
  upper_unbounded : ∀ v, v ∉ M.bounded → upper v = 0
  stationarity : ∀ v,
    (∑ r, y r * M.row r v) + z * M.equality v + lower v + upper v =
      scale * M.objective v
  bound : -2 * scale ≤ (∑ r, y r * M.rhs r) + z + ∑ v ∈ M.bounded, upper v

private theorem sum_upper_eq_bounded (M : Model ρ ν) (D : ScaledDual M) :
    ∑ v, D.upper v = ∑ v ∈ M.bounded, D.upper v := by
  classical
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv =>
    D.upper_unbounded v hv

private theorem stationarity_dot (M : Model ρ ν) (D : ScaledDual M)
    (x : ν → ℤ) :
    D.scale * dot M.objective x =
      (∑ r, D.y r * dot (M.row r) x) +
      D.z * dot M.equality x +
      dot D.lower x +
      dot D.upper x := by
  classical
  calc
    D.scale * dot M.objective x =
        ∑ v, (D.scale * M.objective v) * x v := by
      simp [dot, Finset.mul_sum, mul_assoc]
    _ = ∑ v, ((∑ r, D.y r * M.row r v) +
          D.z * M.equality v + D.lower v + D.upper v) * x v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [D.stationarity v]
    _ = (∑ r, D.y r * dot (M.row r) x) +
          D.z * dot M.equality x + dot D.lower x + dot D.upper x := by
      simp only [add_mul, Finset.sum_add_distrib, dot, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [mul_assoc]

/-- Exact homogeneous weak duality.

Every checked scaled dual certificate gives the lower bound
D * objective(x) ≥ -2 D O for every primal point.
-/
theorem scaledDual_weakDuality (M : Model ρ ν) {O : ℤ}
    (P : Primal M O) (D : ScaledDual M) :
    -2 * D.scale * O ≤ D.scale * dot M.objective P.x := by
  classical
  rw [stationarity_dot M D P.x]
  have hy (r : ρ) :
      D.y r * (M.rhs r * O) ≤ D.y r * dot (M.row r) P.x :=
    mul_le_mul_of_nonpos_left (P.rows r) (D.y_nonpos r)
  have hlo (v : ν) : 0 ≤ D.lower v * P.x v :=
    mul_nonneg (D.lower_nonneg v) (P.nonneg v)
  have hup (v : ν) (hv : v ∈ M.bounded) :
      D.upper v * O ≤ D.upper v * P.x v :=
    mul_le_mul_of_nonpos_left (P.upper v hv) (D.upper_nonpos v)
  have hrows :
      (∑ r, D.y r * M.rhs r) * O ≤
        ∑ r, D.y r * dot (M.row r) P.x := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun r _ => by
      simpa [mul_assoc] using hy r
  have hlower : 0 ≤ dot D.lower P.x := by
    exact Finset.sum_nonneg fun v _ => hlo v
  have hupper :
      (∑ v ∈ M.bounded, D.upper v) * O ≤ dot D.upper P.x := by
    rw [dot, Finset.sum_mul]
    calc
      (∑ v ∈ M.bounded, D.upper v * O) ≤
          ∑ v ∈ M.bounded, D.upper v * P.x v :=
        Finset.sum_le_sum fun v hv => hup v hv
      _ = ∑ v, D.upper v * P.x v := by
        exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by
          rw [D.upper_unbounded v hv]
          simp
  have hdual :
      (-2 * D.scale) * O ≤
        ((∑ r, D.y r * M.rhs r) + D.z +
          ∑ v ∈ M.bounded, D.upper v) * O :=
    mul_le_mul_of_nonneg_right D.bound P.opt_nonneg
  calc
    -2 * D.scale * O = (-2 * D.scale) * O := by ring
    _ ≤ ((∑ r, D.y r * M.rhs r) + D.z +
          ∑ v ∈ M.bounded, D.upper v) * O := hdual
    _ = (∑ r, D.y r * M.rhs r) * O + D.z * O +
          (∑ v ∈ M.bounded, D.upper v) * O := by ring
    _ ≤ (∑ r, D.y r * dot (M.row r) P.x) +
          D.z * dot M.equality P.x + dot D.lower P.x +
          dot D.upper P.x := by
      rw [P.equality]
      linarith

/-- Convert the dual lower bound for objective -G into G ≤ 2 O. -/
theorem length_bound_of_objective (M : Model ρ ν) {O G : ℤ}
    (P : Primal M O) (D : ScaledDual M)
    (hobj : dot M.objective P.x = -G) :
    G ≤ 2 * O := by
  have h := scaledDual_weakDuality M P D
  rw [hobj] at h
  nlinarith [D.scale_pos]

end GreedySuperstring.LP
