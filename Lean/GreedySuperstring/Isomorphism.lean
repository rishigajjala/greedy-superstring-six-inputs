import GreedySuperstring.LP

/-!
# Exact isomorphisms of finite LP models

This module transports primal and scaled-dual witnesses across explicit row
and coordinate equivalences.  It is purely propositional: executable symmetry
checks can instantiate the preservation fields separately.
-/

namespace GreedySuperstring.LP

open scoped BigOperators

variable {ρ₁ ν₁ ρ₂ ν₂ : Type*}
  [Fintype ρ₁] [DecidableEq ρ₁] [Fintype ν₁] [DecidableEq ν₁]
  [Fintype ρ₂] [DecidableEq ρ₂] [Fintype ν₂] [DecidableEq ν₂]

/-- An exact reindexing isomorphism between two finite homogeneous LP models. -/
structure ModelIso (M₁ : Model ρ₁ ν₁) (M₂ : Model ρ₂ ν₂) where
  rowEquiv : ρ₁ ≃ ρ₂
  variableEquiv : ν₁ ≃ ν₂
  row_eq : ∀ row coordinate,
    M₂.row (rowEquiv row) (variableEquiv coordinate) = M₁.row row coordinate
  rhs_eq : ∀ row, M₂.rhs (rowEquiv row) = M₁.rhs row
  equality_eq : ∀ coordinate,
    M₂.equality (variableEquiv coordinate) = M₁.equality coordinate
  objective_eq : ∀ coordinate,
    M₂.objective (variableEquiv coordinate) = M₁.objective coordinate
  bounded_iff : ∀ coordinate,
    variableEquiv coordinate ∈ M₂.bounded ↔ coordinate ∈ M₁.bounded

namespace ModelIso

variable {M₁ : Model ρ₁ ν₁} {M₂ : Model ρ₂ ν₂}

/-- Reindex a coordinate vector from the first model to the second. -/
def mapVector (iso : ModelIso M₁ M₂) (x : ν₁ → ℤ) : ν₂ → ℤ :=
  fun coordinate => x (iso.variableEquiv.symm coordinate)

/-- Reindexing preserves a dot product when its coefficient vector is
preserved by the coordinate equivalence. -/
private theorem dot_mapVector (iso : ModelIso M₁ M₂)
    (a₁ : ν₁ → ℤ) (a₂ : ν₂ → ℤ)
    (coefficients : ∀ coordinate,
      a₂ (iso.variableEquiv coordinate) = a₁ coordinate)
    (x : ν₁ → ℤ) :
    dot a₂ (iso.mapVector x) = dot a₁ x := by
  unfold dot mapVector
  calc
    (∑ coordinate : ν₂, a₂ coordinate * x (iso.variableEquiv.symm coordinate)) =
        ∑ coordinate : ν₁, a₂ (iso.variableEquiv coordinate) *
          x (iso.variableEquiv.symm (iso.variableEquiv coordinate)) := by
      symm
      exact iso.variableEquiv.sum_comp
        (fun coordinate => a₂ coordinate * x (iso.variableEquiv.symm coordinate))
    _ = ∑ coordinate : ν₁, a₁ coordinate * x coordinate := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [iso.variableEquiv.symm_apply_apply, coefficients]

/-- Reversing both equivalences gives the inverse exact model isomorphism. -/
def symm (iso : ModelIso M₁ M₂) : ModelIso M₂ M₁ where
  rowEquiv := iso.rowEquiv.symm
  variableEquiv := iso.variableEquiv.symm
  row_eq := by
    intro row coordinate
    simpa using (iso.row_eq
      (iso.rowEquiv.symm row) (iso.variableEquiv.symm coordinate)).symm
  rhs_eq := by
    intro row
    simpa using (iso.rhs_eq (iso.rowEquiv.symm row)).symm
  equality_eq := by
    intro coordinate
    simpa using (iso.equality_eq (iso.variableEquiv.symm coordinate)).symm
  objective_eq := by
    intro coordinate
    simpa using (iso.objective_eq (iso.variableEquiv.symm coordinate)).symm
  bounded_iff := by
    intro coordinate
    simpa using (iso.bounded_iff (iso.variableEquiv.symm coordinate)).symm

@[simp] theorem symm_symm (iso : ModelIso M₁ M₂) : iso.symm.symm = iso := by
  cases iso
  rfl

/-- The model objective dot product is invariant under exact reindexing. -/
theorem objective_dot_mapVector (iso : ModelIso M₁ M₂) (x : ν₁ → ℤ) :
    dot M₂.objective (iso.mapVector x) = dot M₁.objective x :=
  dot_mapVector iso M₁.objective M₂.objective iso.objective_eq x

/-- Transport a primal feasible point to the isomorphic model. -/
def mapPrimal (iso : ModelIso M₁ M₂) {O : ℤ}
    (primal : Primal M₁ O) : Primal M₂ O where
  x := iso.mapVector primal.x
  opt_nonneg := primal.opt_nonneg
  nonneg := by
    intro coordinate
    exact primal.nonneg (iso.variableEquiv.symm coordinate)
  rows := by
    intro row
    let oldRow := iso.rowEquiv.symm row
    have rowDot :
        dot (M₂.row row) (iso.mapVector primal.x) =
          dot (M₁.row oldRow) primal.x := by
      apply dot_mapVector iso
      intro coordinate
      simpa [oldRow] using iso.row_eq oldRow coordinate
    have rhs : M₂.rhs row = M₁.rhs oldRow := by
      simpa [oldRow] using iso.rhs_eq oldRow
    rw [rowDot, rhs]
    exact primal.rows oldRow
  equality := by
    rw [dot_mapVector iso M₁.equality M₂.equality iso.equality_eq]
    exact primal.equality
  upper := by
    intro coordinate membership
    have oldMembership :
        iso.variableEquiv.symm coordinate ∈ M₁.bounded := by
      apply (iso.bounded_iff (iso.variableEquiv.symm coordinate)).mp
      simpa using membership
    exact primal.upper (iso.variableEquiv.symm coordinate) oldMembership

@[simp] theorem mapPrimal_x (iso : ModelIso M₁ M₂) {O : ℤ}
    (primal : Primal M₁ O) :
    (iso.mapPrimal primal).x = iso.mapVector primal.x := rfl

/-- The objective value of a transported primal point is unchanged. -/
theorem objective_dot_mapPrimal (iso : ModelIso M₁ M₂) {O : ℤ}
    (primal : Primal M₁ O) :
    dot M₂.objective (iso.mapPrimal primal).x =
      dot M₁.objective primal.x :=
  iso.objective_dot_mapVector primal.x

private theorem sum_eq_bounded
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (bounded : Finset ν) (f : ν → ℤ)
    (outside : ∀ coordinate, coordinate ∉ bounded → f coordinate = 0) :
    ∑ coordinate, f coordinate = ∑ coordinate ∈ bounded, f coordinate := by
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun coordinate _ notMem => by
    simpa [outside coordinate notMem]

/-- Transport an exact scaled dual certificate to the isomorphic model. -/
def mapScaledDual (iso : ModelIso M₁ M₂)
    (dual : ScaledDual M₁) : ScaledDual M₂ := by
  have upperOutside : ∀ coordinate : ν₂, coordinate ∉ M₂.bounded →
      dual.upper (iso.variableEquiv.symm coordinate) = 0 := by
    intro coordinate notBounded
    apply dual.upper_unbounded
    intro oldBounded
    apply notBounded
    have mapped := (iso.bounded_iff
      (iso.variableEquiv.symm coordinate)).mpr oldBounded
    simpa using mapped
  have rowBoundSum :
      (∑ row : ρ₂,
          dual.y (iso.rowEquiv.symm row) * M₂.rhs row) =
        ∑ row : ρ₁, dual.y row * M₁.rhs row := by
    calc
      (∑ row : ρ₂, dual.y (iso.rowEquiv.symm row) * M₂.rhs row) =
          ∑ row : ρ₁, dual.y (iso.rowEquiv.symm (iso.rowEquiv row)) *
            M₂.rhs (iso.rowEquiv row) := by
        symm
        exact iso.rowEquiv.sum_comp
          (fun row => dual.y (iso.rowEquiv.symm row) * M₂.rhs row)
      _ = ∑ row : ρ₁, dual.y row * M₁.rhs row := by
        apply Finset.sum_congr rfl
        intro row _
        rw [iso.rowEquiv.symm_apply_apply, iso.rhs_eq]
  have upperBoundSum :
      (∑ coordinate ∈ M₂.bounded,
          dual.upper (iso.variableEquiv.symm coordinate)) =
        ∑ coordinate ∈ M₁.bounded, dual.upper coordinate := by
    calc
      (∑ coordinate ∈ M₂.bounded,
          dual.upper (iso.variableEquiv.symm coordinate)) =
          ∑ coordinate : ν₂,
            dual.upper (iso.variableEquiv.symm coordinate) := by
        symm
        exact sum_eq_bounded M₂.bounded
          (fun coordinate => dual.upper (iso.variableEquiv.symm coordinate))
          upperOutside
      _ = ∑ coordinate : ν₁, dual.upper coordinate := by
        calc
          (∑ coordinate : ν₂, dual.upper (iso.variableEquiv.symm coordinate)) =
              ∑ coordinate : ν₁, dual.upper
                (iso.variableEquiv.symm (iso.variableEquiv coordinate)) := by
            symm
            exact iso.variableEquiv.sum_comp
              (fun coordinate => dual.upper (iso.variableEquiv.symm coordinate))
          _ = ∑ coordinate : ν₁, dual.upper coordinate := by simp
      _ = ∑ coordinate ∈ M₁.bounded, dual.upper coordinate :=
        sum_eq_bounded M₁.bounded dual.upper dual.upper_unbounded
  exact
    { scale := dual.scale
      y := fun row => dual.y (iso.rowEquiv.symm row)
      z := dual.z
      lower := fun coordinate => dual.lower (iso.variableEquiv.symm coordinate)
      upper := fun coordinate => dual.upper (iso.variableEquiv.symm coordinate)
      scale_pos := dual.scale_pos
      y_nonpos := fun row => dual.y_nonpos (iso.rowEquiv.symm row)
      lower_nonneg := fun coordinate =>
        dual.lower_nonneg (iso.variableEquiv.symm coordinate)
      upper_nonpos := fun coordinate =>
        dual.upper_nonpos (iso.variableEquiv.symm coordinate)
      upper_unbounded := upperOutside
      stationarity := by
        intro coordinate
        let oldVariable := iso.variableEquiv.symm coordinate
        have rowSum :
            (∑ row : ρ₂,
                dual.y (iso.rowEquiv.symm row) * M₂.row row coordinate) =
              ∑ row : ρ₁,
                dual.y row * M₁.row row oldVariable := by
          calc
            (∑ row : ρ₂, dual.y (iso.rowEquiv.symm row) * M₂.row row coordinate) =
                ∑ row : ρ₁, dual.y (iso.rowEquiv.symm (iso.rowEquiv row)) *
                  M₂.row (iso.rowEquiv row) coordinate := by
              symm
              exact iso.rowEquiv.sum_comp
                (fun row => dual.y (iso.rowEquiv.symm row) * M₂.row row coordinate)
            _ = ∑ row : ρ₁, dual.y row * M₁.row row oldVariable := by
              apply Finset.sum_congr rfl
              intro row _
              rw [iso.rowEquiv.symm_apply_apply]
              have coefficient :
                  M₂.row (iso.rowEquiv row) coordinate =
                    M₁.row row oldVariable := by
                simpa [oldVariable] using iso.row_eq row oldVariable
              rw [coefficient]
        have equalityCoefficient :
            M₂.equality coordinate = M₁.equality oldVariable := by
          simpa [oldVariable] using iso.equality_eq oldVariable
        have objectiveCoefficient :
            M₂.objective coordinate = M₁.objective oldVariable := by
          simpa [oldVariable] using iso.objective_eq oldVariable
        rw [rowSum, equalityCoefficient, objectiveCoefficient]
        exact dual.stationarity oldVariable
      bound := by
        rw [rowBoundSum, upperBoundSum]
        exact dual.bound }


/-- Transport a primal point in the inverse direction. -/
def unmapPrimal (iso : ModelIso M₁ M₂) {O : ℤ}
    (primal : Primal M₂ O) : Primal M₁ O :=
  iso.symm.mapPrimal primal

/-- Transport a scaled dual in the inverse direction. -/
def unmapScaledDual (iso : ModelIso M₁ M₂)
    (dual : ScaledDual M₂) : ScaledDual M₁ :=
  iso.symm.mapScaledDual dual

/-- A dual certificate for the target model proves factor two for a primal
point of the source model. -/
theorem factorTwo_of_targetDual (iso : ModelIso M₁ M₂) {O G : ℤ}
    (primal : Primal M₁ O) (dual : ScaledDual M₂)
    (objective : dot M₁.objective primal.x = -G) :
    G ≤ 2 * O := by
  apply length_bound_of_objective M₂ (iso.mapPrimal primal) dual
  rw [iso.objective_dot_mapPrimal]
  exact objective

/-- A dual certificate for the source model proves factor two for a primal
point of the target model. -/
theorem factorTwo_of_sourceDual (iso : ModelIso M₁ M₂) {O G : ℤ}
    (primal : Primal M₂ O) (dual : ScaledDual M₁)
    (objective : dot M₂.objective primal.x = -G) :
    G ≤ 2 * O :=
  iso.symm.factorTwo_of_targetDual primal dual objective

end ModelIso

end GreedySuperstring.LP
