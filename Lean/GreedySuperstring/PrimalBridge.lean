import GreedySuperstring.DenseLP
import GreedySuperstring.Relaxation

/-!
# Semantic points as generated dense primals

This module separates two independent obligations in the finite proof.

* Chronology hypotheses contain exactly the mathematical facts contributed
  by a greedy chronology: every emitted dominance comparison, and the two
  cross-edge comparisons licensing every emitted rectangle.
* Dense encoding laws form the small executable-layout boundary. They say
  that generated arrays evaluate as their row tags advertise.

Once those facts are supplied, the literal word lemmas prove every generated
row and construct an LP primal. Rectangle rows are not assumed: they follow
from two cross-edge comparisons and the conditional word rectangle.
-/

namespace GreedySuperstring.PrimalBridge

open GreedySuperstring.Relaxation

variable {α : Type u} {n : ℕ}

/-- A valid off-diagonal edge on Fin n. -/
def EdgeValid (n : ℕ) (edge : Model.Edge) : Prop :=
  edge.src < n ∧ edge.dst < n ∧ edge.src ≠ edge.dst

/-- Total semantic input-length lookup for a raw executable label. -/
def inputLengthAt (data : WordInstance α n) (label : ℕ) : ℕ :=
  if h : label < n then data.inputLength ⟨label, h⟩ else 0

/-- Total semantic overlap lookup for a raw executable edge. -/
def edgeWeight (data : WordInstance α n) (edge : Model.Edge) : ℕ :=
  if hs : edge.src < n then
    if ht : edge.dst < n then
      if _hne : edge.src ≠ edge.dst then
        data.overlap ⟨edge.src, hs⟩ ⟨edge.dst, ht⟩
      else 0
    else 0
  else 0

@[simp] theorem inputLengthAt_of_lt (data : WordInstance α n)
    (label : ℕ) (h : label < n) :
    inputLengthAt data label = data.inputLength ⟨label, h⟩ := by
  simp [inputLengthAt, h]

theorem edgeWeight_of_valid (data : WordInstance α n)
    (edge : Model.Edge) (valid : EdgeValid n edge) :
    edgeWeight data edge =
      data.overlap ⟨edge.src, valid.1⟩ ⟨edge.dst, valid.2.1⟩ := by
  simp [edgeWeight, valid.1, valid.2.1, valid.2.2]

theorem edgeWeight_nonnegative (data : WordInstance α n)
    (edge : Model.Edge) : (0 : ℤ) ≤ edgeWeight data edge := by
  exact_mod_cast Nat.zero_le (edgeWeight data edge)

/-- Integral value of a symbolic generated inequality row. -/
def rowValue (data : WordInstance α n) : Model.RowKind → ℤ
  | .endpointCap edge endpoint =>
      edgeWeight data edge - inputLengthAt data endpoint
  | .triangle i j k =>
      edgeWeight data { src := i, dst := j } +
        edgeWeight data { src := j, dst := k } -
        edgeWeight data { src := i, dst := k } -
        inputLengthAt data j
  | .intervalPair i j =>
      inputLengthAt data i + inputLengthAt data j -
        edgeWeight data { src := i, dst := j } -
        edgeWeight data { src := j, dst := i }
  | .greedyDominance _ selected candidate =>
      edgeWeight data candidate - edgeWeight data selected
  | .licensedRectangle _ selected crossA crossB bottom =>
      edgeWeight data crossA + edgeWeight data crossB -
        edgeWeight data selected - edgeWeight data bottom

/-- Right-hand-side coefficient of OPT advertised by a row tag. -/
def rowRhs : Model.RowKind → ℤ
  | .endpointCap _ _ => 0
  | .triangle _ _ _ => 0
  | .intervalPair _ _ => 1
  | .greedyDominance _ _ _ => 0
  | .licensedRectangle _ _ _ _ _ => 0

/-- Well-formedness facts advertised by generated row tags. -/
def RowShape (n : ℕ) : Model.RowKind → Prop
  | .endpointCap edge endpoint =>
      EdgeValid n edge ∧ (endpoint = edge.src ∨ endpoint = edge.dst)
  | .triangle i j k =>
      i < n ∧ j < n ∧ k < n ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k
  | .intervalPair i j =>
      i < n ∧ j < n ∧ i < j
  | .greedyDominance _ selected candidate =>
      EdgeValid n selected ∧ EdgeValid n candidate
  | .licensedRectangle _ selected crossA crossB bottom =>
      EdgeValid n selected ∧ EdgeValid n crossA ∧
        EdgeValid n crossB ∧ EdgeValid n bottom ∧
        crossA.src = selected.src ∧
        crossB.dst = selected.dst ∧
        bottom.src = crossB.src ∧ bottom.dst = crossA.dst

/-- A tag really occurs among the rows generated for this chronology. -/
def GeneratedKind (n : ℕ) (chronology : List Model.Edge)
    (kind : Model.RowKind) : Prop :=
  ∃ row ∈ Model.inequalityRows n chronology, row.kind = kind

/-- Exactly the chronology-dependent semantic assumptions.

Rectangle fields require only two comparisons against the selected edge.
The conditional word rectangle proves the emitted row. -/
structure ChronologyHypotheses (data : WordInstance α n)
    (chronology : List Model.Edge) : Prop where
  dominance :
    ∀ {step selected candidate},
      GeneratedKind n chronology
        (.greedyDominance step selected candidate) →
      edgeWeight data candidate ≤ edgeWeight data selected
  rectangleCrossCaps :
    ∀ {step selected crossA crossB bottom},
      GeneratedKind n chronology
        (.licensedRectangle step selected crossA crossB bottom) →
      edgeWeight data crossA ≤ edgeWeight data selected ∧
        edgeWeight data crossB ≤ edgeWeight data selected

/-- Executable optimal-path labels corresponding to a semantic order. -/
def optimalPathLabels (order : HamiltonianOrder n) : List ℕ :=
  (order.head :: order.rest).map Fin.val

/-- Exact checker-facing data generated from a chronology and path. -/
def generatedCaseData (chronology : List Model.Edge)
    (order : HamiltonianOrder n) : Model.CaseData :=
  Model.buildCaseData n chronology (optimalPathLabels order)

@[simp] theorem generatedCaseData_nLengths
    (chronology : List Model.Edge) (order : HamiltonianOrder n) :
    (generatedCaseData chronology order).nLengths = n := rfl

/-- Canonical overlap saving used by the generated greedy objective. -/
def canonicalOverlapWeight (data : WordInstance α n) : ℕ :=
  (Model.greedyPathEdges n).map (edgeWeight data) |>.sum

/-- Unnormalized integral value of the canonical greedy output. -/
def greedyLength (data : WordInstance α n) : ℤ :=
  (data.totalInputLength : ℤ) - canonicalOverlapWeight data

/-- A concrete nonnegative vector in generated dense-coordinate order.

Length coordinates are decoded directly. Remaining coordinates are decoded
through the deterministic directed-edge order used by the model. -/
def primalVector (data : WordInstance α n) :
    Fin (Model.variableCount n) → ℤ :=
  fun coordinate =>
    if hlength : coordinate.val < n then
      data.inputLength ⟨coordinate.val, hlength⟩
    else
      match (Model.directedEdges n)[coordinate.val - n]? with
      | none => 0
      | some edge => edgeWeight data edge

theorem primalVector_nonnegative (data : WordInstance α n)
    (coordinate : Fin (Model.variableCount n)) :
    0 ≤ primalVector data coordinate := by
  unfold primalVector
  split
  · exact_mod_cast Nat.zero_le (data.inputLength _)
  · split
    · exact Int.le_refl 0
    · exact edgeWeight_nonnegative data _

theorem primalVector_length (data : WordInstance α n)
    (coordinate : Fin (Model.variableCount n)) (h : coordinate.val < n) :
    primalVector data coordinate = data.inputLength ⟨coordinate.val, h⟩ := by
  simp [primalVector, h]

/-- The semantic vector reindexed to the generated case's variable type. -/
def casePrimalVector (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) :
    DenseLP.VariableIndex (generatedCaseData chronology order) → ℤ :=
  fun coordinate =>
    primalVector data ⟨coordinate.val, by simpa using coordinate.isLt⟩

theorem casePrimalVector_nonnegative (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (coordinate : DenseLP.VariableIndex
      (generatedCaseData chronology order)) :
    0 ≤ casePrimalVector data chronology order coordinate :=
  primalVector_nonnegative data _

theorem casePrimalVector_length (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (coordinate : DenseLP.VariableIndex
      (generatedCaseData chronology order))
    (h : coordinate.val < n) :
    casePrimalVector data chronology order coordinate =
      data.inputLength ⟨coordinate.val, h⟩ := by
  unfold casePrimalVector
  exact primalVector_length data _ h

private theorem denseRowIndex_lt_generatedRows
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex (generatedCaseData chronology order)) :
    row.val < (Model.inequalityRows n chronology).length := by
  simpa [generatedCaseData, Model.buildCaseData,
    Model.CaseModel.toCaseData, Model.CaseModel.matrix,
    Model.buildCaseUnchecked] using row.isLt

/-- The tagged source row corresponding to one dense row coordinate. -/
def generatedRowAt (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex (generatedCaseData chronology order)) :
    Model.Row :=
  (Model.inequalityRows n chronology)[row.val]'(
    denseRowIndex_lt_generatedRows chronology order row)

/-- Canonical symbolic tag decoded from a generated dense row coordinate. -/
def generatedRowKind (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex (generatedCaseData chronology order)) :
    Model.RowKind :=
  (generatedRowAt chronology order row).kind

theorem generatedRowKind_generated
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex (generatedCaseData chronology order)) :
    GeneratedKind n chronology (generatedRowKind chronology order row) := by
  refine ⟨generatedRowAt chronology order row, ?_, rfl⟩
  unfold generatedRowAt
  exact List.getElem_mem
    (denseRowIndex_lt_generatedRows chronology order row)

theorem denseRhs_eq_generatedRowRhs
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex (generatedCaseData chronology order)) :
    (DenseLP.denseModel
        (generatedCaseData chronology order)).rhs row =
      (generatedRowAt chronology order row).rhs := by
  simp [DenseLP.denseModel, DenseLP.denseAt, generatedCaseData,
    Model.buildCaseData, Model.CaseModel.toCaseData,
    Model.CaseModel.rightHandSides, Model.buildCaseUnchecked,
    generatedRowAt]
  rw [List.getElem?_eq_getElem
    (denseRowIndex_lt_generatedRows chronology order row)]
  simp

/-- Layout obligation: every decoded tag has the advertised valid labels. -/
def RowShapeLaw (chronology : List Model.Edge)
    (order : HamiltonianOrder n) : Prop :=
  ∀ row, RowShape n (generatedRowKind chronology order row)

/-- Layout obligation for the generated inequality coefficient arrays. -/
def RowCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) : Prop :=
  ∀ row,
    LP.dot
        ((DenseLP.denseModel
          (generatedCaseData chronology order)).row row)
        (casePrimalVector data chronology order) =
      rowValue data (generatedRowKind chronology order row)

/-- Layout obligation for the generated inequality right-hand sides. -/
def RowRhsLaw (chronology : List Model.Edge)
    (order : HamiltonianOrder n) : Prop :=
  ∀ row,
    (DenseLP.denseModel
        (generatedCaseData chronology order)).rhs row =
      rowRhs (generatedRowKind chronology order row)

/-- Layout obligation for the nominated-path equality array. -/
def EqualityCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) : Prop :=
  LP.dot
      (DenseLP.denseModel
        (generatedCaseData chronology order)).equality
      (casePrimalVector data chronology order) =
    (data.totalInputLength : ℤ) - order.overlapWeight data

/-- Layout obligation for the canonical greedy objective array. -/
def ObjectiveCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) : Prop :=
  LP.dot
      (DenseLP.denseModel
        (generatedCaseData chronology order)).objective
      (casePrimalVector data chronology order) =
    -(data.totalInputLength : ℤ) + canonicalOverlapWeight data

/-- The isolated dense-layout obligation.

No mathematical inequality is hidden here. Each field is an exact equality
between an executable dot product and the expression specified by its tag. -/
structure DenseEncodingLaws (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) where
  shape :
    RowShapeLaw chronology order
  row_dot :
    RowCoefficientLaw data chronology order
  rhs :
    RowRhsLaw chronology order
  equality_dot :
    EqualityCoefficientLaw data chronology order
  objective_dot :
    ObjectiveCoefficientLaw data chronology order

private theorem fin_ne_of_val_ne {a b : ℕ} {ha : a < n} {hb : b < n}
    (hne : a ≠ b) : (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := by
  intro h
  exact hne (congrArg Fin.val h)

/-- A licensed generated rectangle follows from its two cross-edge caps. -/
theorem licensedRectangle_le
    (data : WordInstance α n)
    {step : ℕ} {selected crossA crossB bottom : Model.Edge}
    (shape :
      RowShape n
        (.licensedRectangle step selected crossA crossB bottom))
    (crossCaps :
      edgeWeight data crossA ≤ edgeWeight data selected ∧
        edgeWeight data crossB ≤ edgeWeight data selected) :
    edgeWeight data crossA + edgeWeight data crossB ≤
      edgeWeight data selected + edgeWeight data bottom := by
  rcases selected with ⟨u, v⟩
  rcases crossA with ⟨uA, c⟩
  rcases crossB with ⟨d, vB⟩
  rcases bottom with ⟨dB, cB⟩
  simp only [RowShape] at shape
  rcases shape with
    ⟨hUV, hUAC, hDVB, hDBC, huA, hvB, hdB, hcB⟩
  subst uA
  subst vB
  subst dB
  subst cB
  rcases hUV with ⟨hu, hv, huv⟩
  rcases hUAC with ⟨_, hc, huc⟩
  rcases hDVB with ⟨hd, _, hdv⟩
  rcases hDBC with ⟨_, _, hdc⟩
  let fu : Fin n := ⟨u, hu⟩
  let fv : Fin n := ⟨v, hv⟩
  let fc : Fin n := ⟨c, hc⟩
  let fd : Fin n := ⟨d, hd⟩
  have huvFin : fu ≠ fv := fin_ne_of_val_ne huv
  have hucFin : fu ≠ fc := fin_ne_of_val_ne huc
  have hdvFin : fd ≠ fv := fin_ne_of_val_ne hdv
  have hdcFin : fd ≠ fc := fin_ne_of_val_ne hdc
  have hx :
      data.overlap fu fc ≤ data.overlap fu fv := by
    simpa [edgeWeight, fu, fv, fc, hu, hv, hc, huv, huc] using crossCaps.1
  have hz :
      data.overlap fd fv ≤ data.overlap fu fv := by
    simpa [edgeWeight, fu, fv, fd, hu, hv, hd, huv, hdv] using crossCaps.2
  have rectangle :=
    GreedySuperstring.conditional_directed_rectangle
      (data.maximum fu fv huvFin).1
      (data.maximum fu fc hucFin).1
      (data.maximum fd fv hdvFin).1
      hx hz (data.maximum fd fc hdcFin).2
  simpa [edgeWeight, fu, fv, fc, fd, hu, hv, hc, hd,
    huv, huc, hdv, hdc] using rectangle

/-- Every symbolic generated row is feasible from word facts and chronology. -/
theorem rowValue_le
    (data : WordInstance α n) {chronology : List Model.Edge}
    (chronologySound : ChronologyHypotheses data chronology)
    {kind : Model.RowKind}
    (generated : GeneratedKind n chronology kind)
    (shape : RowShape n kind) :
    rowValue data kind ≤ rowRhs kind * data.optimumLength := by
  cases kind with
  | endpointCap edge endpoint =>
      rcases shape with ⟨valid, rfl | rfl⟩
      · let source : Fin n := ⟨edge.src, valid.1⟩
        let target : Fin n := ⟨edge.dst, valid.2.1⟩
        have hne : source ≠ target := fin_ne_of_val_ne valid.2.2
        have cap := data.overlap_le_source_int hne
        dsimp [source, target] at cap
        rw [rowValue, rowRhs, edgeWeight_of_valid data edge valid,
          inputLengthAt_of_lt data edge.src valid.1]
        omega
      · let source : Fin n := ⟨edge.src, valid.1⟩
        let target : Fin n := ⟨edge.dst, valid.2.1⟩
        have hne : source ≠ target := fin_ne_of_val_ne valid.2.2
        have cap := data.overlap_le_target_int hne
        dsimp [source, target] at cap
        rw [rowValue, rowRhs, edgeWeight_of_valid data edge valid,
          inputLengthAt_of_lt data edge.dst valid.2.1]
        omega
  | triangle i j k =>
      rcases shape with ⟨hi, hj, hk, hij, hik, hjk⟩
      let fi : Fin n := ⟨i, hi⟩
      let fj : Fin n := ⟨j, hj⟩
      let fk : Fin n := ⟨k, hk⟩
      have hijFin : fi ≠ fj :=
        fin_ne_of_val_ne (ha := hi) (hb := hj) hij
      have hjkFin : fj ≠ fk :=
        fin_ne_of_val_ne (ha := hj) (hb := hk) hjk
      have hikFin : fi ≠ fk :=
        fin_ne_of_val_ne (ha := hi) (hb := hk) hik
      have htriangle := data.directed_triangle_int
        hijFin hjkFin hikFin
      have hzero :
          (data.overlap fi fj : ℤ) + data.overlap fj fk -
              data.overlap fi fk - data.inputLength fj ≤ 0 := by
        omega
      simpa [rowValue, rowRhs, edgeWeight, inputLengthAt,
        fi, fj, fk, hi, hj, hk, hij, hik, hjk] using hzero
  | intervalPair i j =>
      rcases shape with ⟨hi, hj, hij⟩
      let fi : Fin n := ⟨i, hi⟩
      let fj : Fin n := ⟨j, hj⟩
      have hijFin : fi ≠ fj :=
        fin_ne_of_val_ne (ha := hi) (hb := hj) (Nat.ne_of_lt hij)
      have hp := data.unordered_pair_int hijFin
      simpa [rowValue, rowRhs, edgeWeight, inputLengthAt,
        fi, fj, hi, hj, Nat.ne_of_lt hij,
        (Nat.ne_of_lt hij).symm] using hp
  | greedyDominance step selected candidate =>
      have h := chronologySound.dominance generated
      simp only [rowValue, rowRhs]
      omega
  | licensedRectangle step selected crossA crossB bottom =>
      have crossCaps := chronologySound.rectangleCrossCaps generated
      have rectangle := licensedRectangle_le data shape crossCaps
      simp only [rowValue, rowRhs]
      omega

/-- The semantic assignment is a primal point of the generated dense case. -/
def primalOf
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (hexact :
      (order.toOverlapPath data).superstring.length = data.optimumLength)
    (chronologySound : ChronologyHypotheses data chronology)
    (encoding : DenseEncodingLaws data chronology order) :
    LP.Primal
      (DenseLP.denseModel (generatedCaseData chronology order))
      (data.optimumLength : ℤ) where
  x := casePrimalVector data chronology order
  opt_nonneg := by
    exact_mod_cast Nat.zero_le data.optimumLength
  nonneg := casePrimalVector_nonnegative data chronology order
  rows := by
    intro row
    rw [encoding.row_dot row, encoding.rhs row]
    exact rowValue_le data chronologySound
      (generatedRowKind_generated chronology order row) (encoding.shape row)
  equality := by
    rw [encoding.equality_dot]
    exact order.optimum_path_normalization_int data hexact
  upper := by
    intro coordinate bounded
    change coordinate ∈
      DenseLP.boundedVariables (generatedCaseData chronology order) at bounded
    have hraw :
        coordinate.val <
          (generatedCaseData chronology order).nLengths :=
      (Finset.mem_filter.mp bounded).2
    have hlength : coordinate.val < n := by
      simpa using hraw
    rw [casePrimalVector_length data chronology order coordinate hlength]
    exact data.inputLength_le_optimumLength_int _

/-- The dense objective is minus the canonical greedy length. -/
theorem objective_identity
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (encoding : DenseEncodingLaws data chronology order) :
    LP.dot
        (DenseLP.denseModel
          (generatedCaseData chronology order)).objective
        (casePrimalVector data chronology order) =
      -greedyLength data := by
  rw [encoding.objective_dot]
  simp only [greedyLength]
  ring

/-- Package the primal point and its objective identity together. -/
theorem exists_primal_with_objective
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (hexact :
      (order.toOverlapPath data).superstring.length = data.optimumLength)
    (chronologySound : ChronologyHypotheses data chronology)
    (encoding : DenseEncodingLaws data chronology order) :
    ∃ primal :
        LP.Primal
          (DenseLP.denseModel (generatedCaseData chronology order))
          (data.optimumLength : ℤ),
      LP.dot
          (DenseLP.denseModel
            (generatedCaseData chronology order)).objective
          primal.x =
        -greedyLength data := by
  refine ⟨primalOf data chronology order hexact chronologySound encoding, ?_⟩
  exact objective_identity data chronology order encoding

end GreedySuperstring.PrimalBridge
