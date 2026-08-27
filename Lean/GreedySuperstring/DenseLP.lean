import GreedySuperstring.Checker
import GreedySuperstring.LP

/-!
# Dense executable cases as generic exact LPs

The executable checker works with arrays and sparse integer records. This
module gives those objects their theorem-level meaning by constructing the
finite generic model and an exact scaled dual certificate.
-/

namespace GreedySuperstring.DenseLP

open scoped BigOperators

abbrev CaseData := Model.CaseData
abbrev Record := Certificate.Record
abbrev SparseEntry := Certificate.SparseEntry

/-- Total access to an integer array. -/
def denseAt (values : Array Int) (index : Nat) : Int :=
  values[index]?.getD 0

/-- Total access to a dense matrix. -/
def matrixAt (rows : Array (Array Int)) (rowIndex variableIndex : Nat) : Int :=
  match rows[rowIndex]? with
  | none => 0
  | some row => denseAt row variableIndex

/-- Finite row coordinates of a rebuilt executable case. -/
abbrev RowIndex (data : CaseData) := Fin data.rows.size

/-- Finite variable coordinates fixed by the string count. -/
abbrev VariableIndex (data : CaseData) :=
  Fin (Model.variableCount data.nLengths)

/-- The length coordinates, which alone have the finite upper bound OPT. -/
def boundedVariables (data : CaseData) : Finset (VariableIndex data) :=
  Finset.univ.filter fun coordinate => coordinate.val < data.nLengths

/-- Generic homogeneous LP represented by executable dense arrays.

Every access remains total even before dimensions are validated. A valid
certificate additionally proves the exact dimensions checked by Checker.
-/
def denseModel (data : CaseData) :
    LP.Model (RowIndex data) (VariableIndex data) where
  row row coordinate := matrixAt data.rows row.val coordinate.val
  rhs row := denseAt data.rhs row.val
  equality coordinate := denseAt data.equality coordinate.val
  objective coordinate := denseAt data.objective coordinate.val
  bounded := boundedVariables data

/-- Sparse integer multiplier interpreted at a dense coordinate. -/
def sparseMultiplier (entries : Array SparseEntry) (index : Nat) : Int :=
  Checker.sparseValue entries index

/-- The theorem-level validity predicate is exactly the checker predicate. -/
abbrev ValidFor (data : CaseData) (record : Record) : Prop :=
  Checker.ValidFor data record

private theorem sparseValid_all {entries : Array SparseEntry} {limit : Nat}
    {sign : Int → Bool} (valid : Checker.SparseValid entries limit sign) :
    entries.all (fun entry =>
      decide (entry.index < limit) && decide (entry.value ≠ 0) &&
        sign entry.value) = true := by
  change Checker.sparseValidBool entries limit sign = true at valid
  rw [Checker.sparseValidBool, Bool.and_eq_true] at valid
  exact valid.2

private theorem sparseValid_range {entries : Array SparseEntry} {limit : Nat}
    {sign : Int → Bool} (valid : Checker.SparseValid entries limit sign) :
    ∀ entry ∈ entries.toList, entry.index < limit := by
  have allEntries := sparseValid_all valid
  have allList :
      entries.toList.all (fun entry =>
        decide (entry.index < limit) && decide (entry.value ≠ 0) &&
          sign entry.value) = true := by
    rw [Array.all_toList]
    exact allEntries
  intro entry membership
  have checked := (List.all_eq_true.mp allList) entry membership
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.1

private theorem sparseValid_sign {entries : Array SparseEntry} {limit : Nat}
    {sign : Int → Bool} (valid : Checker.SparseValid entries limit sign) :
    ∀ entry ∈ entries.toList, sign entry.value = true := by
  have allEntries := sparseValid_all valid
  have allList :
      entries.toList.all (fun entry =>
        decide (entry.index < limit) && decide (entry.value ≠ 0) &&
          sign entry.value) = true := by
    rw [Array.all_toList]
    exact allEntries
  intro entry membership
  have checked := (List.all_eq_true.mp allList) entry membership
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

private theorem sparseValue_eq_sum (entries : Array SparseEntry) (index : Nat) :
    Checker.sparseValue entries index =
      (entries.toList.map fun entry =>
        if entry.index = index then entry.value else 0).sum := by
  unfold Checker.sparseValue
  rw [← Array.foldl_toList]
  have functionsEqual :
      (fun (total : Int) (entry : SparseEntry) =>
        if entry.index = index then total + entry.value else total) =
      (fun (total : Int) (entry : SparseEntry) =>
        total + if entry.index = index then entry.value else 0) := by
    funext total entry
    by_cases matchesIndex : entry.index = index <;> simp [matchesIndex]
  rw [functionsEqual]
  rw [List.sum_eq_foldl, List.foldl_map]

private theorem listSparseDot (entries : List SparseEntry) (limit : Nat)
    (coefficient : Nat → Int)
    (inRange : ∀ entry ∈ entries, entry.index < limit) :
    (∑ coordinate : Fin limit,
      (entries.map fun entry =>
        if entry.index = coordinate.val then entry.value else 0).sum *
          coefficient coordinate.val) =
      (entries.map fun entry =>
        entry.value * coefficient entry.index).sum := by
  classical
  induction entries with
  | nil => simp
  | cons entry remaining inductionHypothesis =>
      have entryRange : entry.index < limit := inRange entry (by simp)
      have remainingRange :
          ∀ item ∈ remaining, item.index < limit := by
        intro item membership
        exact inRange item (by simp [membership])
      let target : Fin limit := ⟨entry.index, entryRange⟩
      have single :
          (∑ coordinate : Fin limit,
            (if entry.index = coordinate.val then entry.value else 0) *
              coefficient coordinate.val) =
            entry.value * coefficient entry.index := by
        calc
          (∑ coordinate : Fin limit,
              (if entry.index = coordinate.val then entry.value else 0) *
                coefficient coordinate.val) =
              ∑ coordinate : Fin limit,
                if coordinate = target then
                  entry.value * coefficient coordinate.val
                else 0 := by
            apply Finset.sum_congr rfl
            intro coordinate _
            by_cases equalsTarget : coordinate = target
            · subst coordinate
              simp [target]
            · have unequalIndex : entry.index ≠ coordinate.val := by
                intro equalIndex
                apply equalsTarget
                apply Fin.ext
                exact equalIndex.symm
              simp [equalsTarget, unequalIndex]
          _ = entry.value * coefficient target.val := by simp
          _ = entry.value * coefficient entry.index := by rfl
      simp only [List.map_cons, List.sum_cons, add_mul,
        Finset.sum_add_distrib]
      rw [single, inductionHypothesis remainingRange]

private theorem sparseDot_eq_fold (entries : Array SparseEntry) (limit : Nat)
    (coefficient : Nat → Int)
    (inRange : ∀ entry ∈ entries.toList, entry.index < limit) :
    (∑ coordinate : Fin limit,
      Checker.sparseValue entries coordinate.val * coefficient coordinate.val) =
      entries.foldl (init := 0) fun total entry =>
        total + entry.value * coefficient entry.index := by
  calc
    (∑ coordinate : Fin limit,
        Checker.sparseValue entries coordinate.val * coefficient coordinate.val) =
        ∑ coordinate : Fin limit,
          (entries.toList.map fun entry =>
            if entry.index = coordinate.val then entry.value else 0).sum *
              coefficient coordinate.val := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [sparseValue_eq_sum]
    _ = (entries.toList.map fun entry =>
          entry.value * coefficient entry.index).sum :=
      listSparseDot entries.toList limit coefficient inRange
    _ = entries.toList.foldl
          (fun total entry =>
            total + entry.value * coefficient entry.index) 0 := by
      rw [List.sum_eq_foldl, List.foldl_map]
    _ = entries.foldl (init := 0) (fun total entry =>
          total + entry.value * coefficient entry.index) :=
      Array.foldl_toList _

private theorem listSum_nonpos {values : List Int}
    (nonpos : ∀ value ∈ values, value ≤ 0) : values.sum ≤ 0 := by
  induction values with
  | nil => simp
  | cons value remaining inductionHypothesis =>
      rw [List.sum_cons]
      exact add_nonpos
        (nonpos value (by simp))
        (inductionHypothesis fun item membership =>
          nonpos item (by simp [membership]))

private theorem sparseValue_nonpos {entries : Array SparseEntry} {limit index : Nat}
    (valid : Checker.SparseValid entries limit
      (fun value => decide (value ≤ 0))) :
    Checker.sparseValue entries index ≤ 0 := by
  rw [sparseValue_eq_sum]
  apply listSum_nonpos
  intro value membership
  rcases List.mem_map.mp membership with ⟨entry, entryMembership, rfl⟩
  have sign := sparseValid_sign valid entry entryMembership
  have nonpos : entry.value ≤ 0 := of_decide_eq_true sign
  by_cases matchesIndex : entry.index = index
  · simpa [matchesIndex] using nonpos
  · simp [matchesIndex]

private theorem sparseValue_nonneg {entries : Array SparseEntry} {limit index : Nat}
    (valid : Checker.SparseValid entries limit
      (fun value => decide (0 ≤ value))) :
    0 ≤ Checker.sparseValue entries index := by
  rw [sparseValue_eq_sum]
  apply List.sum_nonneg
  intro value membership
  rcases List.mem_map.mp membership with ⟨entry, entryMembership, rfl⟩
  have sign := sparseValid_sign valid entry entryMembership
  have nonneg : 0 ≤ entry.value := of_decide_eq_true sign
  by_cases matchesIndex : entry.index = index
  · simpa [matchesIndex] using nonneg
  · simp [matchesIndex]

private theorem sparseValue_eq_zero_of_outside
    {entries : Array SparseEntry} {limit index : Nat} {sign : Int → Bool}
    (valid : Checker.SparseValid entries limit sign)
    (outside : ¬ index < limit) :
    Checker.sparseValue entries index = 0 := by
  rw [sparseValue_eq_sum]
  apply List.sum_eq_zero
  intro value membership
  rcases List.mem_map.mp membership with ⟨entry, entryMembership, rfl⟩
  have entryRange := sparseValid_range valid entry entryMembership
  have unequal : entry.index ≠ index := by
    intro equal
    exact outside (by simpa [equal] using entryRange)
  simp [unequal]

private theorem dimensions_length_le {data : CaseData}
    (valid : Checker.DimensionsValid data) :
    data.nLengths ≤ Model.variableCount data.nLengths := by
  change Checker.dimensionsValidBool data = true at valid
  simp only [Checker.dimensionsValidBool, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at valid
  exact valid.1.2

private structure ValidComponents (data : CaseData) (record : Record) : Prop where
  dimensions : Checker.DimensionsValid data
  scalePositive : 0 < record.scale
  yValid : Checker.SparseValid record.y data.rows.size
    (fun value => decide (value ≤ 0))
  lowerValid : Checker.SparseValid record.lower
    (Model.variableCount data.nLengths) (fun value => decide (0 ≤ value))
  upperValid : Checker.SparseValid record.upper data.nLengths
    (fun value => decide (value ≤ 0))
  stationarity :
    (List.range (Model.variableCount data.nLengths)).all (fun coordinate =>
      Checker.stationarityAt data record coordinate ==
        record.scale * denseAt data.objective coordinate) = true
  encodedBound : Checker.encodedBound data record = record.bound
  bound : -2 * record.scale ≤ record.bound

private theorem componentsOfValid {data : CaseData} {record : Record}
    (valid : ValidFor data record) : ValidComponents data record := by
  change Checker.validForBool data record = true at valid
  simp only [Checker.validForBool, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at valid
  obtain
    ⟨⟨⟨⟨⟨⟨⟨dimensions, scalePositive⟩, yValid⟩, lowerValid⟩,
      upperValid⟩, stationarity⟩, encodedBound⟩, bound⟩ := valid
  exact
    { dimensions := dimensions
      scalePositive := scalePositive
      yValid := yValid
      lowerValid := lowerValid
      upperValid := upperValid
      stationarity := stationarity
      encodedBound := encodedBound
      bound := bound }

/-- Every checker-valid sparse record constructs a generic scaled dual. -/
def scaledDualOfValid (data : CaseData) (record : Record)
    (valid : ValidFor data record) :
    LP.ScaledDual (denseModel data) := by
  let components := componentsOfValid valid
  have dimensionsValid : Checker.DimensionsValid data := components.dimensions
  have ySparse : Checker.SparseValid record.y data.rows.size
      (fun value => decide (value ≤ 0)) := components.yValid
  have lowerSparse : Checker.SparseValid record.lower
      (Model.variableCount data.nLengths)
      (fun value => decide (0 ≤ value)) := components.lowerValid
  have upperSparse : Checker.SparseValid record.upper data.nLengths
      (fun value => decide (value ≤ 0)) := components.upperValid
  let dual : LP.ScaledDual (denseModel data) :=
    { scale := record.scale
      y := fun row => sparseMultiplier record.y row.val
      z := record.z
      lower := fun coordinate => sparseMultiplier record.lower coordinate.val
      upper := fun coordinate => sparseMultiplier record.upper coordinate.val
      scale_pos := components.scalePositive
      y_nonpos := fun row => sparseValue_nonpos ySparse
      lower_nonneg := fun coordinate => sparseValue_nonneg lowerSparse
      upper_nonpos := fun coordinate => sparseValue_nonpos upperSparse
      upper_unbounded := by
        intro coordinate notBounded
        have outside : ¬ coordinate.val < data.nLengths := by
          intro inside
          apply notBounded
          simp [denseModel, boundedVariables, inside]
        exact sparseValue_eq_zero_of_outside upperSparse outside
      stationarity := by
        intro coordinate
        have yRange := sparseValid_range ySparse
        have rowFold :
            (∑ row : RowIndex data,
              sparseMultiplier record.y row.val *
                (denseModel data).row row coordinate) =
              record.y.foldl (init := 0) (fun total entry =>
                total + entry.value *
                  matrixAt data.rows entry.index coordinate.val) := by
          simpa [sparseMultiplier, denseModel] using
            sparseDot_eq_fold record.y data.rows.size
              (fun rowIndex => matrixAt data.rows rowIndex coordinate.val) yRange
        have checkedBool :=
          (List.all_eq_true.mp components.stationarity) coordinate.val
            (List.mem_range.mpr coordinate.isLt)
        have checked :
            Checker.stationarityAt data record coordinate.val =
              record.scale * denseAt data.objective coordinate.val :=
          beq_iff_eq.mp checkedBool
        calc
          (∑ row, sparseMultiplier record.y row.val *
              (denseModel data).row row coordinate) +
                record.z * (denseModel data).equality coordinate +
                sparseMultiplier record.lower coordinate.val +
                sparseMultiplier record.upper coordinate.val =
              Checker.stationarityAt data record coordinate.val := by
            rw [rowFold]
            rfl
          _ = record.scale * denseAt data.objective coordinate.val := checked
          _ = record.scale * (denseModel data).objective coordinate := rfl
      bound := by
        have yRange := sparseValid_range ySparse
        have rowFold :
            (∑ row : RowIndex data,
              sparseMultiplier record.y row.val *
                (denseModel data).rhs row) =
              record.y.foldl (init := 0) (fun total entry =>
                total + entry.value * denseAt data.rhs entry.index) := by
          simpa [sparseMultiplier, denseModel] using
            sparseDot_eq_fold record.y data.rows.size
              (fun rowIndex => denseAt data.rhs rowIndex) yRange
        have lengthLe := dimensions_length_le dimensionsValid
        have upperRange :
            ∀ entry ∈ record.upper.toList,
              entry.index < Model.variableCount data.nLengths := by
          intro entry membership
          exact lt_of_lt_of_le
            (sparseValid_range upperSparse entry membership) lengthLe
        have upperFoldAll := sparseDot_eq_fold record.upper
          (Model.variableCount data.nLengths) (fun _ => 1) upperRange
        have upperOutside :
            ∀ coordinate : VariableIndex data,
              coordinate ∉ (denseModel data).bounded →
                sparseMultiplier record.upper coordinate.val = 0 := by
          intro coordinate notBounded
          have outside : ¬ coordinate.val < data.nLengths := by
            intro inside
            apply notBounded
            simp [denseModel, boundedVariables, inside]
          exact sparseValue_eq_zero_of_outside upperSparse outside
        have boundedSum :
            (∑ coordinate ∈ (denseModel data).bounded,
                sparseMultiplier record.upper coordinate.val) =
              ∑ coordinate : VariableIndex data,
                sparseMultiplier record.upper coordinate.val := by
          exact Finset.sum_subset (Finset.subset_univ _) fun coordinate _ outside =>
            upperOutside coordinate outside
        have upperFold :
            (∑ coordinate : VariableIndex data,
                sparseMultiplier record.upper coordinate.val) =
              record.upper.foldl (init := 0) fun total entry =>
                total + entry.value := by
          simpa [sparseMultiplier] using upperFoldAll
        calc
          -2 * record.scale ≤ record.bound := components.bound
          _ = Checker.encodedBound data record := components.encodedBound.symm
          _ = (∑ row : RowIndex data,
                  sparseMultiplier record.y row.val *
                    (denseModel data).rhs row) +
                record.z +
                ∑ coordinate ∈ (denseModel data).bounded,
                  sparseMultiplier record.upper coordinate.val := by
            rw [rowFold, boundedSum, upperFold]
            rfl }
  exact dual

@[simp] theorem scaledDualOfValid_scale (data : CaseData) (record : Record)
    (valid : ValidFor data record) :
    (scaledDualOfValid data record valid).scale = record.scale := rfl

/-- A valid dense certificate proves the generic weak-duality lower bound. -/
theorem objectiveLowerBound {data : CaseData} {record : Record} {O : Int}
    (valid : ValidFor data record)
    (primal : LP.Primal (denseModel data) O) :
    -2 * record.scale * O ≤
      record.scale * LP.dot (denseModel data).objective primal.x :=
  by
    have bound := LP.scaledDual_weakDuality (denseModel data) primal
      (scaledDualOfValid data record valid)
    simpa using bound

/-- Factor-two conclusion for every primal point of a checker-valid dense case. -/
theorem factorTwo {data : CaseData} {record : Record} {O G : Int}
    (valid : ValidFor data record)
    (primal : LP.Primal (denseModel data) O)
    (objective : LP.dot (denseModel data).objective primal.x = -G) :
    G ≤ 2 * O :=
  LP.length_bound_of_objective (denseModel data) primal
    (scaledDualOfValid data record valid) objective

/-- Direct end-to-end form starting from executable checker acceptance. -/
theorem factorTwo_of_checkRecord {data : CaseData} {record : Record}
    {O G : Int}
    (accepted : Checker.checkRecord data record = .ok ())
    (primal : LP.Primal (denseModel data) O)
    (objective : LP.dot (denseModel data).objective primal.x = -G) :
    G ≤ 2 * O :=
  factorTwo (Checker.checkRecord_sound accepted) primal objective

end GreedySuperstring.DenseLP
