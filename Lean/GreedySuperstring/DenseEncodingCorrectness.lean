import GreedySuperstring.PrimalBridge

/-!
# Correctness of the executable dense encoding

This module proves that the theorem-friendly symbolic interpretation in
`PrimalBridge` is exactly the dense array layout emitted by `Model`.  It does
not alter the executable builder.  In particular, the private coefficient
accumulator is mirrored definitionally and then verified by a generic
array-update dot-product theorem.
-/

namespace GreedySuperstring.DenseEncodingCorrectness

open scoped BigOperators
open GreedySuperstring.Relaxation

variable {α : Type u} {n : Nat}

/-! ## The directed-edge coordinate order -/

private def edgeRow (n source : Nat) : List Model.Edge :=
  (List.range n).filterMap fun target =>
    if source = target then none
    else some { src := source, dst := target }

private theorem directedEdges_eq_edgeRows (n : Nat) :
    Model.directedEdges n = (List.range n).flatMap (edgeRow n) := by
  unfold Model.directedEdges Model.vertices edgeRow
  apply congrArg (fun f => (List.range n).flatMap f)
  funext source
  congr 1
  funext target
  simp

private theorem filterMap_excluding_of_not_mem
    (source : Nat) (values : List Nat) (hnot : source ∉ values) :
    values.filterMap (fun target =>
      if source = target then none else some target) = values := by
  induction values with
  | nil => rfl
  | cons target rest ih =>
      have hne : source ≠ target := by
        intro h
        apply hnot
        simp [h]
      have hnotRest : source ∉ rest := by
        intro h
        exact hnot (by simp [h])
      simp [hne, ih hnotRest]

private theorem edgeRow_eq_map_excluding (n source : Nat) :
    edgeRow n source =
      ((List.range n).filterMap fun target =>
        if source = target then none else some target).map
          fun target => ({ src := source, dst := target } : Model.Edge) := by
  unfold edgeRow
  induction List.range n with
  | nil => rfl
  | cons target rest ih =>
      simp only [List.filterMap_cons]
      by_cases h : source = target
      · rw [if_pos h, if_pos h]
        exact ih
      · rw [if_neg h, if_neg h, List.map_cons]
        exact congrArg
          (fun tail => ({ src := source, dst := target } : Model.Edge) :: tail) ih

private theorem range_decomp (n source : Nat) (hs : source < n) :
    List.range n = List.range source ++
      source :: List.range' (source + 1) (n - (source + 1)) := by
  have hsum : n = source + (n - source) := by omega
  have hsub : n - source = (n - (source + 1)) + 1 := by omega
  calc
    List.range n = List.range' 0 (source + (n - source)) := by
      rw [List.range_eq_range']
      exact congrArg (List.range' 0) hsum
    _ = List.range' 0 source ++ List.range' source (n - source) := by
      simpa using (List.range'_append (s := 0) (m := source)
        (n := n - source) (step := 1)).symm
    _ = List.range' 0 source ++ source ::
          List.range' (source + 1) (n - (source + 1)) := by
      rw [hsub, List.range'_succ]
    _ = List.range source ++ source ::
          List.range' (source + 1) (n - (source + 1)) := by
      rw [List.range_eq_range']

private theorem edgeRow_decomp (n source : Nat) (hs : source < n) :
    edgeRow n source =
      (List.range source).map
          (fun target => ({ src := source, dst := target } : Model.Edge)) ++
      (List.range' (source + 1) (n - (source + 1))).map
          (fun target => ({ src := source, dst := target } : Model.Edge)) := by
  rw [edgeRow_eq_map_excluding, range_decomp n source hs]
  simp only [List.filterMap_append, List.filterMap_cons, ↓reduceIte,
    List.map_append, List.map_nil, List.append_nil]
  have hprefix : source ∉ List.range source := by simp
  have hsuffix : source ∉
      List.range' (source + 1) (n - (source + 1)) := by
    intro membership
    rw [List.mem_range'] at membership
    rcases membership with ⟨i, hi, heq⟩
    omega
  rw [filterMap_excluding_of_not_mem source _ hprefix,
    filterMap_excluding_of_not_mem source _ hsuffix]

private theorem edgeRow_length (n source : Nat) (hs : source < n) :
    (edgeRow n source).length = n - 1 := by
  rw [edgeRow_decomp n source hs, List.length_append,
    List.length_map, List.length_range, List.length_map,
    List.length_range']
  omega

private theorem edgeRow_get (n source target : Nat)
    (hs : source < n) (ht : target < n) (hne : source ≠ target) :
    (edgeRow n source)[if target < source then target else target - 1]? =
      some ({ src := source, dst := target } : Model.Edge) := by
  rw [edgeRow_decomp n source hs]
  by_cases hlt : target < source
  · rw [if_pos hlt, List.getElem?_append_left]
    · simp [List.getElem?_map, List.getElem?_range hlt]
    · simp [hlt]
  · have hgreater : source < target := by omega
    have hprefix : source ≤ target - 1 := by omega
    have hlocal : target - 1 - source < n - (source + 1) := by omega
    rw [if_neg hlt, List.getElem?_append_right]
    · simp only [List.length_map, List.length_range]
      rw [List.getElem?_map, List.getElem?_range' hlocal]
      simp
      omega
    · simpa using hprefix

private theorem flatMap_edgeRows_prefix_length (n source : Nat)
    (hs : source < n) :
    ((List.range source).flatMap (edgeRow n)).length = source * (n - 1) := by
  rw [List.length_flatMap]
  have hmap :
      (List.range source).map (fun i => (edgeRow n i).length) =
        (List.range source).map (fun _ => n - 1) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact edgeRow_length n i (hi.trans hs)
  rw [hmap]
  simp

private theorem directedEdges_get (n source target : Nat)
    (hs : source < n) (ht : target < n) (hne : source ≠ target) :
    (Model.directedEdges n)[source * (n - 1) +
      (if target < source then target else target - 1)]? =
      some ({ src := source, dst := target } : Model.Edge) := by
  rw [directedEdges_eq_edgeRows, range_decomp n source hs,
    List.flatMap_append, List.flatMap_cons]
  have hprefix := flatMap_edgeRows_prefix_length n source hs
  have hlocal :
      (if target < source then target else target - 1) < n - 1 := by
    split <;> omega
  rw [List.getElem?_append_right]
  · rw [hprefix]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left]
    · exact edgeRow_get n source target hs ht hne
    · rw [edgeRow_length n source hs]
      exact hlocal
  · rw [hprefix]
    omega

/-- The executable lexicographic edge list is inverse to `overlapIndex`. -/
theorem directedEdges_get_overlapIndex (n : Nat) (edge : Model.Edge)
    (valid : PrimalBridge.EdgeValid n edge) :
    (Model.directedEdges n)[Model.overlapIndex n edge - n]? = some edge := by
  rcases edge with ⟨source, target⟩
  have hindex :
      Model.overlapIndex n { src := source, dst := target } - n =
        source * (n - 1) +
          (if target < source then target else target - 1) := by
    simp only [Model.overlapIndex]
    omega
  rw [hindex]
  exact directedEdges_get n source target valid.1 valid.2.1 valid.2.2

/-- A valid overlap coordinate lies inside the dense variable array. -/
theorem overlapIndex_lt_variableCount (n : Nat) (edge : Model.Edge)
    (valid : PrimalBridge.EdgeValid n edge) :
    Model.overlapIndex n edge < Model.variableCount n := by
  rcases edge with ⟨source, target⟩
  rcases valid with ⟨hsource, htarget, hne⟩
  change source < n at hsource
  change target < n at htarget
  change source ≠ target at hne
  have hn : 2 ≤ n := by omega
  have hpositive : 0 < n - 1 := by omega
  have hlocal :
      (if target < source then target else target - 1) < n - 1 := by
    split <;> omega
  have hblock :
      source * (n - 1) +
          (if target < source then target else target - 1) <
        n * (n - 1) := by
    have hwithin :
        source * (n - 1) +
            (if target < source then target else target - 1) <
          (source + 1) * (n - 1) := by
      calc
        source * (n - 1) +
            (if target < source then target else target - 1) <
            source * (n - 1) + (n - 1) := Nat.add_lt_add_left hlocal _
        _ = (source + 1) * (n - 1) := by ring
    exact hwithin.trans_le
      (Nat.mul_le_mul_right (n - 1) (Nat.succ_le_of_lt hsource))
  simp only [Model.overlapIndex, Model.variableCount]
  omega

/-! ## Generic correctness of the coefficient accumulator -/

private def arrayDot (n : Nat) (coefficients : Model.Coefficients)
    (x : Fin (Model.variableCount n) → Int) : Int :=
  ∑ coordinate, Model.coefficientAt coefficients coordinate.val * x coordinate

private def termValue (n : Nat) (x : Fin (Model.variableCount n) → Int)
    (term : Model.Variable × Int) : Int :=
  match Model.variableIndex? n term.1 with
  | none => 0
  | some index =>
      if h : index < Model.variableCount n then
        term.2 * x ⟨index, h⟩
      else 0

private def addTerm (n : Nat) (coefficients : Model.Coefficients)
    (term : Model.Variable × Int) : Model.Coefficients :=
  match Model.variableIndex? n term.1 with
  | none => coefficients
  | some index => Model.addCoefficient coefficients index term.2

private def termsCoefficients (n : Nat)
    (terms : List (Model.Variable × Int)) : Model.Coefficients :=
  terms.foldl (addTerm n)
    (Array.replicate (Model.variableCount n) 0)

private theorem addTerm_size (n : Nat) (coefficients : Model.Coefficients)
    (term : Model.Variable × Int) :
    (addTerm n coefficients term).size = coefficients.size := by
  unfold addTerm
  split <;> simp [Model.addCoefficient]

private theorem foldl_addTerm_size (n : Nat)
    (terms : List (Model.Variable × Int))
    (coefficients : Model.Coefficients) :
    (terms.foldl (addTerm n) coefficients).size = coefficients.size := by
  induction terms generalizing coefficients with
  | nil => rfl
  | cons term rest ih =>
      rw [List.foldl_cons, ih, addTerm_size]

private theorem termsCoefficients_size (n : Nat)
    (terms : List (Model.Variable × Int)) :
    (termsCoefficients n terms).size = Model.variableCount n := by
  unfold termsCoefficients
  rw [foldl_addTerm_size]
  simp

private theorem arrayDot_addCoefficient (n : Nat)
    (coefficients : Model.Coefficients) (index : Nat) (delta : Int)
    (x : Fin (Model.variableCount n) → Int)
    (hsize : coefficients.size = Model.variableCount n) :
    arrayDot n (Model.addCoefficient coefficients index delta) x =
      arrayDot n coefficients x +
        if h : index < Model.variableCount n then delta * x ⟨index, h⟩ else 0 := by
  classical
  by_cases hindex : index < Model.variableCount n
  · have hindexArray : index < coefficients.size := by simpa [hsize] using hindex
    have pointwise (coordinate : Fin (Model.variableCount n)) :
        Model.coefficientAt (Model.addCoefficient coefficients index delta)
            coordinate.val =
          Model.coefficientAt coefficients coordinate.val +
            if index = coordinate.val then delta else 0 := by
      have hcoordinateArray : coordinate.val < coefficients.size := by
        simpa [hsize] using coordinate.isLt
      rw [Model.addCoefficient, Model.coefficientAt,
        Array.getElem?_setIfInBounds]
      by_cases heq : index = coordinate.val <;>
        simp [heq, hcoordinateArray, Model.coefficientAt]
    rw [arrayDot, arrayDot]
    simp only [pointwise, add_mul, Finset.sum_add_distrib]
    congr 1
    calc
      (∑ coordinate : Fin (Model.variableCount n),
          (if index = coordinate.val then delta else 0) * x coordinate) =
          ∑ coordinate : Fin (Model.variableCount n),
            if coordinate = ⟨index, hindex⟩ then delta * x coordinate else 0 := by
            apply Finset.sum_congr rfl
            intro coordinate _
            by_cases heq : coordinate = ⟨index, hindex⟩
            · subst coordinate
              simp
            · have hval : index ≠ coordinate.val := by
                intro h
                apply heq
                exact Fin.ext h.symm
              simp [heq, hval]
      _ = delta * x ⟨index, hindex⟩ := by simp
      _ = (if h : index < Model.variableCount n then
              delta * x ⟨index, h⟩ else 0) := by
            simp [hindex]
  · have hindexArray : ¬ index < coefficients.size := by simpa [hsize] using hindex
    have unchanged :
        Model.addCoefficient coefficients index delta = coefficients := by
      simp [Model.addCoefficient, Array.setIfInBounds, hindexArray]
    rw [unchanged]
    simp [hindex]

private theorem foldl_addTerm_dot (n : Nat)
    (terms : List (Model.Variable × Int))
    (coefficients : Model.Coefficients)
    (x : Fin (Model.variableCount n) → Int)
    (hsize : coefficients.size = Model.variableCount n) :
    arrayDot n (terms.foldl (addTerm n) coefficients) x =
      arrayDot n coefficients x + (terms.map (termValue n x)).sum := by
  induction terms generalizing coefficients with
  | nil => simp
  | cons term rest ih =>
      rw [List.foldl_cons, ih]
      · simp only [List.map_cons, List.sum_cons]
        unfold addTerm
        split <;> rename_i hindex
        · simp [termValue, hindex]
        · rw [arrayDot_addCoefficient (hsize := hsize)]
          simp [termValue, hindex]
          ring
      · exact (addTerm_size n coefficients term).trans hsize

private theorem termsCoefficients_dot (n : Nat)
    (terms : List (Model.Variable × Int))
    (x : Fin (Model.variableCount n) → Int) :
    arrayDot n (termsCoefficients n terms) x =
      (terms.map (termValue n x)).sum := by
  unfold termsCoefficients
  rw [foldl_addTerm_dot n terms _ x (by simp)]
  have hzero :
      arrayDot n (Array.replicate (Model.variableCount n) 0) x = 0 := by
    unfold arrayDot
    apply Finset.sum_eq_zero
    intro coordinate _
    have hrep : coordinate.val <
        (Array.replicate (Model.variableCount n) (0 : Int)).size := by
      simpa using coordinate.isLt
    rw [Model.coefficientAt, Array.getElem?_eq_getElem hrep]
    simp
  rw [hzero, zero_add]

/-- Public-row mirror with the same runtime representation as `Model.makeRow`. -/
private def rowFromTerms (n : Nat) (rhs : Int) (kind : Model.RowKind)
    (terms : List (Model.Variable × Int)) : Model.Row :=
  { coefficients := termsCoefficients n terms
    rhs := rhs
    kind := kind }


/-! ## Semantic values at the executable coordinates -/

private theorem primalVector_overlap (data : WordInstance α n)
    (edge : Model.Edge) (valid : PrimalBridge.EdgeValid n edge) :
    PrimalBridge.primalVector data
      ⟨Model.overlapIndex n edge,
        overlapIndex_lt_variableCount n edge valid⟩ =
      PrimalBridge.edgeWeight data edge := by
  have hge : n ≤ Model.overlapIndex n edge := by
    unfold Model.overlapIndex
    omega
  simp [PrimalBridge.primalVector, not_lt_of_ge hge,
    directedEdges_get_overlapIndex n edge valid]

private theorem termValue_length (data : WordInstance α n)
    (vertex : Nat) (coefficient : Int) :
    termValue n (PrimalBridge.primalVector data)
        (.length vertex, coefficient) =
      coefficient * PrimalBridge.inputLengthAt data vertex := by
  by_cases hvertex : vertex < n
  · have hcount : vertex < Model.variableCount n := by
      simp only [Model.variableCount]
      omega
    simp [termValue, Model.variableIndex?, hvertex, hcount,
      PrimalBridge.primalVector, PrimalBridge.inputLengthAt]
  · simp [termValue, Model.variableIndex?, hvertex,
      PrimalBridge.inputLengthAt]

private theorem termValue_overlap (data : WordInstance α n)
    (edge : Model.Edge) (coefficient : Int)
    (valid : PrimalBridge.EdgeValid n edge) :
    termValue n (PrimalBridge.primalVector data)
        (.overlap edge, coefficient) =
      coefficient * PrimalBridge.edgeWeight data edge := by
  simp [termValue, Model.variableIndex?, valid.1, valid.2.1, valid.2.2,
    overlapIndex_lt_variableCount n edge valid,
    primalVector_overlap data edge valid]

private theorem rowFromTerms_dot (data : WordInstance α n)
    (rhs : Int) (kind : Model.RowKind)
    (terms : List (Model.Variable × Int)) :
    arrayDot n (rowFromTerms n rhs kind terms).coefficients
        (PrimalBridge.primalVector data) =
      (terms.map (termValue n (PrimalBridge.primalVector data))).sum := by
  exact termsCoefficients_dot n terms (PrimalBridge.primalVector data)



/-! ## Definitionally exact theorem-friendly row mirrors -/

private def endpointCapRows (n : Nat) : List Model.Row :=
  (Model.directedEdges n).flatMap fun edge =>
    [edge.src, edge.dst].map fun endpoint =>
      rowFromTerms n 0 (.endpointCap edge endpoint)
        [(.overlap edge, 1), (.length endpoint, -1)]

private def triangleRows (n : Nat) : List Model.Row :=
  (Model.vertices n).flatMap fun i =>
    (Model.vertices n).flatMap fun j =>
      (Model.vertices n).filterMap fun k =>
        if i ≠ j ∧ i ≠ k ∧ j ≠ k then
          let ij : Model.Edge := { src := i, dst := j }
          let jk : Model.Edge := { src := j, dst := k }
          let ik : Model.Edge := { src := i, dst := k }
          some <| rowFromTerms n 0 (.triangle i j k)
            [(.overlap ij, 1), (.overlap jk, 1),
              (.overlap ik, -1), (.length j, -1)]
        else
          none

private def intervalPairRows (n : Nat) : List Model.Row :=
  (Model.vertices n).flatMap fun i =>
    (Model.vertices n).filterMap fun j =>
      if i < j then
        let ij : Model.Edge := { src := i, dst := j }
        let ji : Model.Edge := { src := j, dst := i }
        some <| rowFromTerms n 1 (.intervalPair i j)
          [(.length i, 1), (.length j, 1),
            (.overlap ij, -1), (.overlap ji, -1)]
      else
        none

private def greedyDominanceRows (n step : Nat) (selected : Model.Edge)
    (feasible : List Model.Edge) : List Model.Row :=
  (feasible.filter fun candidate => !(candidate == selected)).map fun candidate =>
    rowFromTerms n 0 (.greedyDominance step selected candidate)
      [(.overlap candidate, 1), (.overlap selected, -1)]

private def hasLoop (edge : Model.Edge) : Bool := edge.src == edge.dst

private def licensedRectangleRows (n step : Nat) (selected : Model.Edge)
    (feasible : List Model.Edge) : List Model.Row :=
  (Model.vertices n).flatMap fun uPrime =>
    (Model.vertices n).filterMap fun vPrime =>
      let crossA : Model.Edge := { src := selected.src, dst := vPrime }
      let crossB : Model.Edge := { src := uPrime, dst := selected.dst }
      let bottom : Model.Edge := { src := uPrime, dst := vPrime }
      if hasLoop selected || hasLoop crossA || hasLoop crossB || hasLoop bottom then
        none
      else if feasible.contains crossA && feasible.contains crossB then
        some <| rowFromTerms n 0
          (.licensedRectangle step selected crossA crossB bottom)
          [(.overlap crossA, 1), (.overlap crossB, 1),
            (.overlap selected, -1), (.overlap bottom, -1)]
      else
        none

private def greedyRowsAux (n : Nat) (chosen : List Model.Edge) (step : Nat) :
    List Model.Edge → List Model.Row
  | [] => []
  | selected :: remaining =>
      let feasible := Model.feasibleEdges n chosen
      greedyDominanceRows n step selected feasible ++
        licensedRectangleRows n step selected feasible ++
        greedyRowsAux n (chosen ++ [selected]) (step + 1) remaining

private def greedyRows (n : Nat) (order : List Model.Edge) : List Model.Row :=
  greedyRowsAux n [] 0 order

private def inequalityRows (n : Nat) (order : List Model.Edge) : List Model.Row :=
  endpointCapRows n ++ triangleRows n ++ intervalPairRows n ++
    greedyRows n order

private theorem endpointCapRows_eq (n : Nat) :
    Model.endpointCapRows n = endpointCapRows n := by
  with_unfolding_all rfl

private theorem triangleRows_eq (n : Nat) :
    Model.triangleRows n = triangleRows n := by
  with_unfolding_all rfl

private theorem intervalPairRows_eq (n : Nat) :
    Model.intervalPairRows n = intervalPairRows n := by
  with_unfolding_all rfl

private theorem greedyDominanceRows_eq (n step : Nat)
    (selected : Model.Edge) (feasible : List Model.Edge) :
    Model.greedyDominanceRows n step selected feasible =
      greedyDominanceRows n step selected feasible := by
  with_unfolding_all rfl

private theorem licensedRectangleRows_eq (n step : Nat)
    (selected : Model.Edge) (feasible : List Model.Edge) :
    Model.licensedRectangleRows n step selected feasible =
      licensedRectangleRows n step selected feasible := by
  with_unfolding_all rfl

private theorem greedyRowsFrom_eq (n : Nat) (chosen : List Model.Edge)
    (step : Nat) (order : List Model.Edge) :
    Model.greedyRowsFrom n chosen step order =
      greedyRowsAux n chosen step order := by
  induction order generalizing chosen step with
  | nil => simp [greedyRowsAux]
  | cons selected remaining ih =>
      rw [Model.greedyRowsFrom_cons]
      simp only [greedyRowsAux]
      rw [greedyDominanceRows_eq, licensedRectangleRows_eq, ih]

private theorem greedyRows_eq (n : Nat) (order : List Model.Edge) :
    Model.greedyRows n order = greedyRows n order := by
  calc
    Model.greedyRows n order = Model.greedyRowsFrom n [] 0 order :=
      Model.greedyRows_eq_from n order
    _ = greedyRowsAux n [] 0 order := greedyRowsFrom_eq n [] 0 order
    _ = greedyRows n order := rfl

private theorem inequalityRows_eq (n : Nat) (order : List Model.Edge) :
    Model.inequalityRows n order = inequalityRows n order := by
  unfold Model.inequalityRows inequalityRows
  rw [endpointCapRows_eq, triangleRows_eq, intervalPairRows_eq,
    greedyRows_eq]


private theorem pathEquality_eq (n : Nat) (path : List Nat) :
    Model.pathEquality n path =
      termsCoefficients n
        ((Model.vertices n).map (fun i => (.length i, 1)) ++
          (Model.pathEdges path).map (fun edge => (.overlap edge, -1))) := by
  with_unfolding_all rfl

private theorem greedyObjective_eq (n : Nat) :
    Model.greedyObjective n =
      termsCoefficients n
        ((Model.vertices n).map (fun i => (.length i, -1)) ++
          (Model.greedyPathEdges n).map (fun edge => (.overlap edge, 1))) := by
  with_unfolding_all rfl



/-! ## Correctness of every generated source row -/

private theorem directedEdge_valid {n : Nat} {edge : Model.Edge}
    (membership : edge ∈ Model.directedEdges n) :
    PrimalBridge.EdgeValid n edge := by
  simp [Model.directedEdges, Model.vertices] at membership
  rcases membership with ⟨source, hsource, target, htarget, hne, rfl⟩
  exact ⟨hsource, htarget, hne⟩

private theorem feasibleEdge_valid {n : Nat} {chosen : List Model.Edge}
    {edge : Model.Edge} (membership : edge ∈ Model.feasibleEdges n chosen) :
    PrimalBridge.EdgeValid n edge := by
  rw [Model.feasibleEdges, List.mem_filter] at membership
  rcases membership with ⟨_, feasible⟩
  simp [Model.feasibleEdge, Model.validEdge] at feasible
  rcases feasible with
    ⟨⟨⟨⟨⟨hsource, htarget⟩, hne⟩, _⟩, _⟩, _⟩
  exact ⟨hsource, htarget, hne⟩

private structure SourceRowLaws (data : WordInstance α n)
    (row : Model.Row) : Prop where
  dot : arrayDot n row.coefficients (PrimalBridge.primalVector data) =
    PrimalBridge.rowValue data row.kind
  rhs : row.rhs = PrimalBridge.rowRhs row.kind
  shape : PrimalBridge.RowShape n row.kind

private theorem endpointRow_laws (data : WordInstance α n)
    (edge : Model.Edge) (endpoint : Nat)
    (valid : PrimalBridge.EdgeValid n edge)
    (endpoint_eq : endpoint = edge.src ∨ endpoint = edge.dst) :
    SourceRowLaws data
      (rowFromTerms n 0 (.endpointCap edge endpoint)
        [(.overlap edge, 1), (.length endpoint, -1)]) := by
  refine ⟨?_, rfl, ⟨valid, endpoint_eq⟩⟩
  rw [rowFromTerms_dot]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [termValue_overlap data edge 1 valid,
    termValue_length data endpoint (-1)]
  simp only [rowFromTerms, PrimalBridge.rowValue]
  ring

private theorem triangleRow_laws (data : WordInstance α n)
    (i j k : Nat) (hi : i < n) (hj : j < n) (hk : k < n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    SourceRowLaws data
      (rowFromTerms n 0 (.triangle i j k)
        [(.overlap { src := i, dst := j }, 1),
          (.overlap { src := j, dst := k }, 1),
          (.overlap { src := i, dst := k }, -1),
          (.length j, -1)]) := by
  let ij : Model.Edge := { src := i, dst := j }
  let jk : Model.Edge := { src := j, dst := k }
  let ik : Model.Edge := { src := i, dst := k }
  have vij : PrimalBridge.EdgeValid n ij := ⟨hi, hj, hij⟩
  have vjk : PrimalBridge.EdgeValid n jk := ⟨hj, hk, hjk⟩
  have vik : PrimalBridge.EdgeValid n ik := ⟨hi, hk, hik⟩
  refine ⟨?_, rfl, ⟨hi, hj, hk, hij, hik, hjk⟩⟩
  rw [rowFromTerms_dot]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [termValue_overlap data ij 1 vij,
    termValue_overlap data jk 1 vjk,
    termValue_overlap data ik (-1) vik,
    termValue_length data j (-1)]
  simp only [rowFromTerms, PrimalBridge.rowValue]
  ring

private theorem intervalPairRow_laws (data : WordInstance α n)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    SourceRowLaws data
      (rowFromTerms n 1 (.intervalPair i j)
        [(.length i, 1), (.length j, 1),
          (.overlap { src := i, dst := j }, -1),
          (.overlap { src := j, dst := i }, -1)]) := by
  let ij : Model.Edge := { src := i, dst := j }
  let ji : Model.Edge := { src := j, dst := i }
  have vij : PrimalBridge.EdgeValid n ij := ⟨hi, hj, Nat.ne_of_lt hij⟩
  have vji : PrimalBridge.EdgeValid n ji := ⟨hj, hi, (Nat.ne_of_lt hij).symm⟩
  refine ⟨?_, rfl, ⟨hi, hj, hij⟩⟩
  rw [rowFromTerms_dot]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [termValue_length data i 1, termValue_length data j 1,
    termValue_overlap data ij (-1) vij,
    termValue_overlap data ji (-1) vji]
  simp only [rowFromTerms, PrimalBridge.rowValue]
  ring

private theorem dominanceRow_laws (data : WordInstance α n)
    (step : Nat) (selected candidate : Model.Edge)
    (selectedValid : PrimalBridge.EdgeValid n selected)
    (candidateValid : PrimalBridge.EdgeValid n candidate) :
    SourceRowLaws data
      (rowFromTerms n 0 (.greedyDominance step selected candidate)
        [(.overlap candidate, 1), (.overlap selected, -1)]) := by
  refine ⟨?_, rfl, ⟨selectedValid, candidateValid⟩⟩
  rw [rowFromTerms_dot]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [termValue_overlap data candidate 1 candidateValid,
    termValue_overlap data selected (-1) selectedValid]
  simp only [rowFromTerms, PrimalBridge.rowValue]
  ring

private theorem rectangleRow_laws (data : WordInstance α n)
    (step : Nat) (selected crossA crossB bottom : Model.Edge)
    (selectedValid : PrimalBridge.EdgeValid n selected)
    (crossAValid : PrimalBridge.EdgeValid n crossA)
    (crossBValid : PrimalBridge.EdgeValid n crossB)
    (bottomValid : PrimalBridge.EdgeValid n bottom)
    (crossA_src : crossA.src = selected.src)
    (crossB_dst : crossB.dst = selected.dst)
    (bottom_src : bottom.src = crossB.src)
    (bottom_dst : bottom.dst = crossA.dst) :
    SourceRowLaws data
      (rowFromTerms n 0
        (.licensedRectangle step selected crossA crossB bottom)
        [(.overlap crossA, 1), (.overlap crossB, 1),
          (.overlap selected, -1), (.overlap bottom, -1)]) := by
  refine ⟨?_, rfl, ⟨selectedValid, crossAValid, crossBValid,
    bottomValid, crossA_src, crossB_dst, bottom_src, bottom_dst⟩⟩
  rw [rowFromTerms_dot]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [termValue_overlap data crossA 1 crossAValid,
    termValue_overlap data crossB 1 crossBValid,
    termValue_overlap data selected (-1) selectedValid,
    termValue_overlap data bottom (-1) bottomValid]
  simp only [rowFromTerms, PrimalBridge.rowValue]
  ring

private theorem endpointCapRows_laws (data : WordInstance α n)
    {row : Model.Row} (membership : row ∈ endpointCapRows n) :
    SourceRowLaws data row := by
  rw [endpointCapRows, List.mem_flatMap] at membership
  rcases membership with ⟨edge, edgeMem, endpointMem⟩
  rcases List.mem_map.mp endpointMem with ⟨endpoint, endpointIn, rowEq⟩
  have endpointEq : endpoint = edge.src ∨ endpoint = edge.dst := by
    simpa using endpointIn
  rw [← rowEq]
  exact endpointRow_laws data edge endpoint
    (directedEdge_valid edgeMem) endpointEq

private theorem triangleRows_laws (data : WordInstance α n)
    {row : Model.Row} (membership : row ∈ triangleRows n) :
    SourceRowLaws data row := by
  rw [triangleRows, List.mem_flatMap] at membership
  rcases membership with ⟨i, iMem, membership⟩
  rw [List.mem_flatMap] at membership
  rcases membership with ⟨j, jMem, membership⟩
  rw [List.mem_filterMap] at membership
  rcases membership with ⟨k, kMem, rowEq⟩
  by_cases distinct : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · simp [distinct] at rowEq
    subst row
    have hi : i < n := by simpa [Model.vertices] using iMem
    have hj : j < n := by simpa [Model.vertices] using jMem
    have hk : k < n := by simpa [Model.vertices] using kMem
    exact triangleRow_laws data i j k hi hj hk
      distinct.1 distinct.2.1 distinct.2.2
  · simp [distinct] at rowEq

private theorem intervalPairRows_laws (data : WordInstance α n)
    {row : Model.Row} (membership : row ∈ intervalPairRows n) :
    SourceRowLaws data row := by
  rw [intervalPairRows, List.mem_flatMap] at membership
  rcases membership with ⟨i, iMem, membership⟩
  rw [List.mem_filterMap] at membership
  rcases membership with ⟨j, jMem, rowEq⟩
  by_cases hij : i < j
  · simp [hij] at rowEq
    subst row
    have hi : i < n := by simpa [Model.vertices] using iMem
    have hj : j < n := by simpa [Model.vertices] using jMem
    exact intervalPairRow_laws data i j hi hj hij
  · simp [hij] at rowEq

private theorem greedyDominanceRows_laws (data : WordInstance α n)
    (step : Nat) (selected : Model.Edge) (feasible : List Model.Edge)
    (selectedValid : PrimalBridge.EdgeValid n selected)
    (feasibleValid : ∀ edge ∈ feasible, PrimalBridge.EdgeValid n edge)
    {row : Model.Row} (membership :
      row ∈ greedyDominanceRows n step selected feasible) :
    SourceRowLaws data row := by
  rw [greedyDominanceRows] at membership
  rcases List.mem_map.mp membership with ⟨candidate, candidateMem, rfl⟩
  have feasibleMem : candidate ∈ feasible := (List.mem_filter.mp candidateMem).1
  exact dominanceRow_laws data step selected candidate selectedValid
    (feasibleValid candidate feasibleMem)

private theorem licensedRectangleRows_laws (data : WordInstance α n)
    (step : Nat) (selected : Model.Edge) (feasible : List Model.Edge)
    (selectedValid : PrimalBridge.EdgeValid n selected)
    (feasibleValid : ∀ edge ∈ feasible, PrimalBridge.EdgeValid n edge)
    {row : Model.Row} (membership :
      row ∈ licensedRectangleRows n step selected feasible) :
    SourceRowLaws data row := by
  rw [licensedRectangleRows, List.mem_flatMap] at membership
  rcases membership with ⟨uPrime, uMem, membership⟩
  rw [List.mem_filterMap] at membership
  rcases membership with ⟨vPrime, vMem, rowEq⟩
  let crossA : Model.Edge := { src := selected.src, dst := vPrime }
  let crossB : Model.Edge := { src := uPrime, dst := selected.dst }
  let bottom : Model.Edge := { src := uPrime, dst := vPrime }
  by_cases loops :
      (hasLoop selected || hasLoop crossA || hasLoop crossB || hasLoop bottom) = true
  · simp [crossA, crossB, bottom, loops] at rowEq
  · have loopsFalse :
        (hasLoop selected || hasLoop crossA || hasLoop crossB ||
          hasLoop bottom) = false := Bool.eq_false_of_not_eq_true loops
    by_cases crosses :
        (feasible.contains crossA && feasible.contains crossB) = true
    · have rowFacts :
          (crossA ∈ feasible ∧ crossB ∈ feasible) ∧
            rowFromTerms n 0
                (.licensedRectangle step selected crossA crossB bottom)
                [(.overlap crossA, 1), (.overlap crossB, 1),
                  (.overlap selected, -1), (.overlap bottom, -1)] = row := by
        simpa [crossA, crossB, bottom, loopsFalse] using rowEq
      rcases rowFacts with ⟨⟨crossAMem, crossBMem⟩, rowEqPrime⟩
      rw [← rowEqPrime]
      have crossAValid := feasibleValid crossA crossAMem
      have crossBValid := feasibleValid crossB crossBMem
      have hu : uPrime < n := by simpa [Model.vertices] using uMem
      have hv : vPrime < n := by simpa [Model.vertices] using vMem
      have loopFacts := loopsFalse
      simp [hasLoop, crossA, crossB, bottom] at loopFacts
      rcases loopFacts with ⟨⟨⟨_, _⟩, _⟩, bottomNe⟩
      have bottomValid : PrimalBridge.EdgeValid n bottom :=
        ⟨hu, hv, bottomNe⟩
      exact rectangleRow_laws data step selected crossA crossB bottom
        selectedValid crossAValid crossBValid bottomValid rfl rfl rfl rfl
    · have rowFacts :
          (crossA ∈ feasible ∧ crossB ∈ feasible) ∧
            rowFromTerms n 0
                (.licensedRectangle step selected crossA crossB bottom)
                [(.overlap crossA, 1), (.overlap crossB, 1),
                  (.overlap selected, -1), (.overlap bottom, -1)] = row := by
        simpa [crossA, crossB, bottom, loopsFalse] using rowEq
      have crossesTrue :
          (feasible.contains crossA && feasible.contains crossB) = true := by
        simp [List.contains_iff_mem, rowFacts.1.1, rowFacts.1.2]
      exact (crosses crossesTrue).elim


private theorem greedyRowsAux_laws (data : WordInstance α n)
    (chosen : List Model.Edge) (step : Nat) (order : List Model.Edge)
    (validOrder : ∀ edge ∈ order, PrimalBridge.EdgeValid n edge)
    {row : Model.Row} (membership : row ∈ greedyRowsAux n chosen step order) :
    SourceRowLaws data row := by
  induction order generalizing chosen step row with
  | nil => simp [greedyRowsAux] at membership
  | cons selected remaining ih =>
      have selectedValid : PrimalBridge.EdgeValid n selected :=
        validOrder selected (by simp)
      have remainingValid :
          ∀ edge ∈ remaining, PrimalBridge.EdgeValid n edge := by
        intro edge edgeMem
        exact validOrder edge (by simp [edgeMem])
      have feasibleValid :
          ∀ edge ∈ Model.feasibleEdges n chosen,
            PrimalBridge.EdgeValid n edge := by
        intro edge edgeMem
        exact feasibleEdge_valid edgeMem
      simp only [greedyRowsAux] at membership
      rcases List.mem_append.mp membership with currentMem | remainingMem
      · rcases List.mem_append.mp currentMem with dominanceMem | rectangleMem
        · exact greedyDominanceRows_laws data step selected
            (Model.feasibleEdges n chosen) selectedValid feasibleValid dominanceMem
        · exact licensedRectangleRows_laws data step selected
            (Model.feasibleEdges n chosen) selectedValid feasibleValid rectangleMem
      · exact ih (chosen ++ [selected]) (step + 1) remainingValid remainingMem

private theorem inequalityRows_laws (data : WordInstance α n)
    (order : List Model.Edge)
    (validOrder : ∀ edge ∈ order, PrimalBridge.EdgeValid n edge)
    {row : Model.Row} (membership : row ∈ Model.inequalityRows n order) :
    SourceRowLaws data row := by
  rw [inequalityRows_eq, inequalityRows] at membership
  rcases List.mem_append.mp membership with staticMem | greedyMem
  · rcases List.mem_append.mp staticMem with firstMem | pairMem
    · rcases List.mem_append.mp firstMem with endpointMem | triangleMem
      · exact endpointCapRows_laws data endpointMem
      · exact triangleRows_laws data triangleMem
    · exact intervalPairRows_laws data pairMem
  · exact greedyRowsAux_laws data [] 0 order validOrder greedyMem

/-! ## Dense-coordinate bridge -/

private theorem generatedRowAt_mem
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex
      (PrimalBridge.generatedCaseData chronology order)) :
    PrimalBridge.generatedRowAt chronology order row ∈
      Model.inequalityRows n chronology := by
  have rowBound : row.val < (Model.inequalityRows n chronology).length := by
    simpa [PrimalBridge.generatedCaseData, Model.buildCaseData,
      Model.CaseModel.toCaseData, Model.CaseModel.matrix,
      Model.buildCaseUnchecked] using row.isLt
  unfold PrimalBridge.generatedRowAt
  exact List.getElem_mem rowBound

private theorem denseRow_dot_eq_arrayDot
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (row : DenseLP.RowIndex
      (PrimalBridge.generatedCaseData chronology order)) :
    LP.dot
        ((DenseLP.denseModel
          (PrimalBridge.generatedCaseData chronology order)).row row)
        (PrimalBridge.casePrimalVector data chronology order) =
      arrayDot n
        (PrimalBridge.generatedRowAt chronology order row).coefficients
        (PrimalBridge.primalVector data) := by
  have rowBound : row.val < (Model.inequalityRows n chronology).length := by
    simpa [PrimalBridge.generatedCaseData, Model.buildCaseData,
      Model.CaseModel.toCaseData, Model.CaseModel.matrix,
      Model.buildCaseUnchecked] using row.isLt
  simp [LP.dot, arrayDot, DenseLP.denseModel, DenseLP.matrixAt,
    DenseLP.denseAt, PrimalBridge.generatedCaseData,
    Model.buildCaseData, Model.CaseModel.toCaseData,
    Model.CaseModel.matrix, Model.buildCaseUnchecked,
    PrimalBridge.generatedRowAt, Model.coefficientAt,
    PrimalBridge.casePrimalVector, List.getElem?_eq_getElem rowBound]
  rfl

private theorem rowShapeLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (validChronology :
      ∀ edge ∈ chronology, PrimalBridge.EdgeValid n edge) :
    PrimalBridge.RowShapeLaw chronology order := by
  intro row
  have laws := inequalityRows_laws data chronology validChronology
    (generatedRowAt_mem chronology order row)
  simpa [PrimalBridge.generatedRowKind] using laws.shape

private theorem rowCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (validChronology :
      ∀ edge ∈ chronology, PrimalBridge.EdgeValid n edge) :
    PrimalBridge.RowCoefficientLaw data chronology order := by
  intro row
  rw [denseRow_dot_eq_arrayDot]
  have laws := inequalityRows_laws data chronology validChronology
    (generatedRowAt_mem chronology order row)
  simpa [PrimalBridge.generatedRowKind] using laws.dot

private theorem rowRhsLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n)
    (validChronology :
      ∀ edge ∈ chronology, PrimalBridge.EdgeValid n edge) :
    PrimalBridge.RowRhsLaw chronology order := by
  intro row
  rw [PrimalBridge.denseRhs_eq_generatedRowRhs]
  have laws := inequalityRows_laws data chronology validChronology
    (generatedRowAt_mem chronology order row)
  simpa [PrimalBridge.generatedRowKind] using laws.rhs

private theorem denseEquality_dot_eq_arrayDot
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n) :
    LP.dot
        (DenseLP.denseModel
          (PrimalBridge.generatedCaseData chronology order)).equality
        (PrimalBridge.casePrimalVector data chronology order) =
      arrayDot n
        (Model.pathEquality n (PrimalBridge.optimalPathLabels order))
        (PrimalBridge.primalVector data) := by
  simp [LP.dot, arrayDot, DenseLP.denseModel, DenseLP.denseAt,
    PrimalBridge.generatedCaseData, Model.buildCaseData,
    Model.CaseModel.toCaseData, Model.buildCaseUnchecked,
    Model.coefficientAt, PrimalBridge.casePrimalVector]
  rfl

private theorem denseObjective_dot_eq_arrayDot
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n) :
    LP.dot
        (DenseLP.denseModel
          (PrimalBridge.generatedCaseData chronology order)).objective
        (PrimalBridge.casePrimalVector data chronology order) =
      arrayDot n (Model.greedyObjective n)
        (PrimalBridge.primalVector data) := by
  simp [LP.dot, arrayDot, DenseLP.denseModel, DenseLP.denseAt,
    PrimalBridge.generatedCaseData, Model.buildCaseData,
    Model.CaseModel.toCaseData, Model.buildCaseUnchecked,
    Model.coefficientAt, PrimalBridge.casePrimalVector]
  rfl

private theorem inputLengths_range_eq (data : WordInstance α n) :
    (List.range n).map (PrimalBridge.inputLengthAt data) =
      List.ofFn data.inputLength := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    rw [List.getElem_map, List.getElem_range,
      List.getElem_ofFn]
    have indexBound : index < n := by simpa using leftBound
    simp [PrimalBridge.inputLengthAt, indexBound]

private theorem lengthTerms_sum (data : WordInstance α n)
    (coefficient : Int) :
    ((Model.vertices n).map fun vertex =>
        termValue n (PrimalBridge.primalVector data)
          (.length vertex, coefficient)).sum =
      coefficient * (data.totalInputLength : Int) := by
  simp_rw [termValue_length]
  unfold Model.vertices
  rw [List.sum_map_mul_left]
  have casted :
      ((List.range n).map fun vertex =>
          (PrimalBridge.inputLengthAt data vertex : Int)).sum =
        (data.totalInputLength : Int) := by
    have mapped :
        ((List.range n).map (PrimalBridge.inputLengthAt data)).map
            (fun value : Nat => (value : Int)) =
          (List.range n).map fun vertex =>
            (PrimalBridge.inputLengthAt data vertex : Int) := by
      simp [List.map_map, Function.comp_def]
    rw [← mapped, inputLengths_range_eq]
    simp [WordInstance.totalInputLength]
  rw [casted]

private theorem pathTerms_sum (data : WordInstance α n)
    (head : Fin n) (rest : List (Fin n))
    (nodup : (head :: rest).Nodup) :
    ((Model.pathEdges ((head :: rest).map Fin.val)).map fun edge =>
        termValue n (PrimalBridge.primalVector data)
          (.overlap edge, -1)).sum =
      -(pathWeight data.overlap head rest : Int) := by
  induction rest generalizing head with
  | nil => simp [Model.pathEdges, pathWeight]
  | cons next remaining ih =>
      have tailNodup : (next :: remaining).Nodup :=
        (List.nodup_cons.mp nodup).2
      have headNeNext : head ≠ next := by
        intro equal
        subst next
        exact (List.nodup_cons.mp nodup).1 (by simp)
      let edge : Model.Edge := { src := head.val, dst := next.val }
      have edgeValid : PrimalBridge.EdgeValid n edge :=
        ⟨head.isLt, next.isLt, fun equal =>
          headNeNext (Fin.ext equal)⟩
      calc
        ((Model.pathEdges ((head :: next :: remaining).map Fin.val)).map
            fun current =>
              termValue n (PrimalBridge.primalVector data)
                (.overlap current, -1)).sum =
            -(PrimalBridge.edgeWeight data edge : Int) +
              ((Model.pathEdges ((next :: remaining).map Fin.val)).map
                fun current =>
                  termValue n (PrimalBridge.primalVector data)
                    (.overlap current, -1)).sum := by
          simp [Model.pathEdges, edge,
            termValue_overlap data edge (-1) edgeValid]
        _ = -(PrimalBridge.edgeWeight data edge : Int) -
              (pathWeight data.overlap next remaining : Int) := by
          rw [ih next tailNodup]
          ring
        _ = -(pathWeight data.overlap head (next :: remaining) : Int) := by
          rw [PrimalBridge.edgeWeight_of_valid data edge edgeValid]
          simp only [pathWeight, Nat.cast_add]
          ring

private theorem greedyPathEdge_valid {edge : Model.Edge}
    (membership : edge ∈ Model.greedyPathEdges n) :
    PrimalBridge.EdgeValid n edge := by
  rw [Model.greedyPathEdges] at membership
  rcases List.mem_map.mp membership with ⟨source, sourceMem, rfl⟩
  have sourceBound : source < n - 1 := List.mem_range.mp sourceMem
  change source < n ∧ source + 1 < n ∧ source ≠ source + 1
  exact ⟨by omega, by omega, by omega⟩

private theorem greedyTerms_sum (data : WordInstance α n) :
    ((Model.greedyPathEdges n).map fun edge =>
        termValue n (PrimalBridge.primalVector data)
          (.overlap edge, 1)).sum =
      (PrimalBridge.canonicalOverlapWeight data : Int) := by
  have mapped :
      (Model.greedyPathEdges n).map (fun edge =>
          termValue n (PrimalBridge.primalVector data)
            (.overlap edge, 1)) =
        (Model.greedyPathEdges n).map (fun edge =>
          (PrimalBridge.edgeWeight data edge : Int)) := by
    apply List.map_congr_left
    intro edge membership
    rw [termValue_overlap data edge 1
      (greedyPathEdge_valid membership)]
    simp
  rw [mapped]
  simp [PrimalBridge.canonicalOverlapWeight, Function.comp_def]

private theorem equalityCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) :
    PrimalBridge.EqualityCoefficientLaw data chronology order := by
  unfold PrimalBridge.EqualityCoefficientLaw
  rw [denseEquality_dot_eq_arrayDot, pathEquality_eq,
    termsCoefficients_dot, List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def]
  rw [lengthTerms_sum data 1]
  rw [PrimalBridge.optimalPathLabels,
    pathTerms_sum data order.head order.rest order.nodup]
  simp only [HamiltonianOrder.overlapWeight]
  ring

private theorem objectiveCoefficientLaw (data : WordInstance α n)
    (chronology : List Model.Edge) (order : HamiltonianOrder n) :
    PrimalBridge.ObjectiveCoefficientLaw data chronology order := by
  unfold PrimalBridge.ObjectiveCoefficientLaw
  rw [denseObjective_dot_eq_arrayDot, greedyObjective_eq,
    termsCoefficients_dot, List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def]
  rw [lengthTerms_sum data (-1), greedyTerms_sum]
  ring

/-- Every executable dense case has exactly the symbolic interpretation used
by `PrimalBridge`, provided the supplied chronology consists of valid raw
edges. No row inequality or certificate fact is assumed by this theorem. -/
theorem denseEncodingLaws
    (data : WordInstance α n) (chronology : List Model.Edge)
    (order : HamiltonianOrder n)
    (validChronology :
      ∀ edge ∈ chronology, PrimalBridge.EdgeValid n edge) :
    PrimalBridge.DenseEncodingLaws data chronology order where
  shape := rowShapeLaw data chronology order validChronology
  row_dot := rowCoefficientLaw data chronology order validChronology
  rhs := rowRhsLaw data chronology order validChronology
  equality_dot := equalityCoefficientLaw data chronology order
  objective_dot := objectiveCoefficientLaw data chronology order


end GreedySuperstring.DenseEncodingCorrectness
