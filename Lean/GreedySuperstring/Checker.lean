import GreedySuperstring.Certificate
import GreedySuperstring.Model

/-!
# Exact certificate replay

This module is the trusted computational boundary for the finite LP corpora.
It uses only integer arithmetic, rebuilds every positional case, and checks
the complete denominator-cleared dual identity.  The JSON/gzip converter is
not trusted.
-/

namespace GreedySuperstring.Checker

open GreedySuperstring

abbrev Record := Certificate.Record
abbrev SparseEntry := Certificate.SparseEntry
abbrev CaseData := Model.CaseData

/-- SHA-256 of the checked-in five-input JSON corpus. -/
def fiveSourceSha256 : String :=
  "e733e5cb361e515db6fe257789f3991bf5f264a3f241814d9a74464439b0fe66"

/-- SHA-256 of the checked-in compressed six-input JSONL corpus. -/
def sixSourceSha256 : String :=
  "53ef042c6c7b4c59ca2beac9b960fcd99ea522956d3212efdbd122a35119ab01"

private def intAt (values : Array Int) (index : Nat) : Int :=
  values[index]?.getD 0

/-- Dense value represented by a sparse integer vector.

Malformed duplicates are added here and rejected separately by `SparseValid`.
This makes every lookup total even before validation.
-/
def sparseValue (entries : Array SparseEntry) (index : Nat) : Int :=
  entries.foldl (init := 0) fun total entry =>
    if entry.index = index then total + entry.value else total

private def rowCoefficient (data : CaseData) (rowIndex variableIndex : Nat) : Int :=
  match data.rows[rowIndex]? with
  | none => 0
  | some row => intAt row variableIndex

/-- The denominator-cleared stationarity left-hand side at one variable. -/
def stationarityAt (data : CaseData) (record : Record)
    (variableIndex : Nat) : Int :=
  let rowContribution := record.y.foldl (init := 0) fun total entry =>
    total + entry.value * rowCoefficient data entry.index variableIndex
  rowContribution + record.z * intAt data.equality variableIndex +
    sparseValue record.lower variableIndex + sparseValue record.upper variableIndex

/-- The denominator-cleared dual objective encoded by a record. -/
def encodedBound (data : CaseData) (record : Record) : Int :=
  let rowContribution := record.y.foldl (init := 0) fun total entry =>
    total + entry.value * intAt data.rhs entry.index
  let upperContribution := record.upper.foldl (init := 0) fun total entry =>
    total + entry.value
  rowContribution + record.z + upperContribution

private def increasingAfter (previous : Nat) : List SparseEntry → Bool
  | [] => true
  | entry :: remaining =>
      decide (previous < entry.index) &&
        increasingAfter entry.index remaining

private def strictlyIncreasingIndices : List SparseEntry → Bool
  | [] => true
  | entry :: remaining => increasingAfter entry.index remaining

/-- Executable shape, range, nonzero, and sign test for a sparse vector. -/
def sparseValidBool (entries : Array SparseEntry) (limit : Nat)
    (sign : Int → Bool) : Bool :=
  strictlyIncreasingIndices entries.toList &&
    entries.all (fun entry =>
      decide (entry.index < limit) && decide (entry.value ≠ 0) &&
        sign entry.value)

/-- Declarative reflection of the exact sparse-vector conditions. -/
def SparseValid (entries : Array SparseEntry) (limit : Nat)
    (sign : Int → Bool) : Prop :=
  sparseValidBool entries limit sign = true

/-- Executable test that all dense arrays have the model dimensions. -/
def dimensionsValidBool (data : CaseData) : Bool :=
  let variableCount := Model.variableCount data.nLengths
  data.rows.size == data.rhs.size &&
    data.equality.size == variableCount &&
    data.objective.size == variableCount &&
    decide (data.nLengths ≤ variableCount) &&
    data.rows.all (fun row => row.size == variableCount)

/-- Declarative reflection of the exact dense-dimension conditions. -/
def DimensionsValid (data : CaseData) : Prop :=
  dimensionsValidBool data = true

/-- Exact declarative conditions checked for one scaled dual certificate.

The sparse vectors represent integer numerators over the common positive
`scale`.  Thus stationarity is checked after multiplying the integral primal
objective by `scale`, with no rational arithmetic or rounding.
-/
def validForBool (data : CaseData) (record : Record) : Bool :=
  let variableCount := Model.variableCount data.nLengths
  dimensionsValidBool data &&
    decide (0 < record.scale) &&
    sparseValidBool record.y data.rows.size (fun value => decide (value ≤ 0)) &&
    sparseValidBool record.lower variableCount (fun value => decide (0 ≤ value)) &&
    sparseValidBool record.upper data.nLengths (fun value => decide (value ≤ 0)) &&
    (List.range variableCount).all (fun variableIndex =>
      stationarityAt data record variableIndex ==
        record.scale * intAt data.objective variableIndex) &&
    encodedBound data record == record.bound &&
    decide (-2 * record.scale ≤ record.bound)

/-- Exact declarative reflection of all checks for one scaled dual. -/
def ValidFor (data : CaseData) (record : Record) : Prop :=
  validForBool data record = true

/-- Total executable checker for one certificate and rebuilt LP case. -/
def checkRecord (data : CaseData) (record : Record) : Except String Unit :=
  if validForBool data record then
    .ok ()
  else
    .error "certificate fails dimensions, sparse signs/ranges, stationarity, or bound"

/-- Checker acceptance reflects to the exact declarative certificate conditions. -/
theorem checkRecord_sound {data : CaseData} {record : Record}
    (accepted : checkRecord data record = .ok ()) : ValidFor data record := by
  unfold checkRecord at accepted
  unfold ValidFor
  cases valid : validForBool data record with
  | false => simp [valid] at accepted
  | true => rfl

/-- Every declaratively valid certificate is accepted by the executable checker. -/
theorem checkRecord_complete {data : CaseData} {record : Record}
    (valid : ValidFor data record) : checkRecord data record = .ok () := by
  unfold ValidFor at valid
  simp [checkRecord, valid]

private def validateHeader (header : Certificate.Header)
    (records : Array Record) (expectedKind : String) (expectedN expectedCount : Nat)
    (expectedHash : String) : Except String Unit := do
  if header.kind ≠ expectedKind then
    throw s!"expected {expectedKind} certificate header, found {header.kind}"
  if header.n ≠ expectedN then
    throw s!"expected dimension {expectedN}, found {header.n}"
  if header.count ≠ expectedCount then
    throw s!"expected header count {expectedCount}, found {header.count}"
  if records.size ≠ expectedCount then
    throw s!"expected {expectedCount} records, found {records.size}"
  if header.sourceSha256 ≠ expectedHash then
    throw "source-corpus SHA-256 differs from the pinned digest"

private def checkPathsForOrder (n : Nat) (base : CaseData)
    (records : Array Record) : List (List Nat) → Nat → Except String Nat
  | [], recordIndex => pure recordIndex
  | path :: remaining, recordIndex => do
      if !Model.validOptimalPath n path then
        throw s!"case {recordIndex}: generated optimum path is invalid"
      let some record := records[recordIndex]?
        | throw s!"case {recordIndex}: missing positional certificate"
      let data : CaseData := { base with equality := Model.pathEquality n path }
      match checkRecord data record with
      | .error message => throw s!"case {recordIndex}: {message}"
      | .ok () =>
          checkPathsForOrder n base records remaining (recordIndex + 1)

private def checkOrders (n : Nat) (paths : List (List Nat))
    (records : Array Record) : List (List Model.Edge) → Nat → Except String Nat
  | [], recordIndex => pure recordIndex
  | order :: remaining, recordIndex => do
      if !Model.validGreedyOrder n order then
        throw s!"case {recordIndex}: generated greedy order is invalid"
      let firstPath ← match paths with
        | [] => throw "empty optimum-path enumeration"
        | path :: _ => pure path
      let some base := Model.buildCaseData? n order firstPath
        | throw s!"case {recordIndex}: checked case construction failed"
      let nextIndex ← checkPathsForOrder n base records paths recordIndex
      checkOrders n paths records remaining nextIndex

/-- Replay a rectangular chronology/path enumeration against records in
row-major positional order. -/
def checkPositionalCases (n : Nat) (orders : List (List Model.Edge))
    (paths : List (List Nat)) (records : Array Record) : Except String Nat := do
  let expectedCount := orders.length * paths.length
  if records.size ≠ expectedCount then
    throw s!"case enumeration expects {expectedCount} records, found {records.size}"
  let checked ← checkOrders n paths records orders 0
  if checked ≠ expectedCount then
    throw s!"case replay stopped at {checked} of {expectedCount} records"
  pure checked

private theorem buildCaseData?_eq_some
    {n : Nat} {order : List Model.Edge} {path : List Nat}
    {data : CaseData}
    (built : Model.buildCaseData? n order path = some data) :
    data = Model.buildCaseData n order path := by
  unfold Model.buildCaseData? Model.buildCase? at built
  cases valid : Model.validCaseInput n order path <;> simp [valid] at built
  exact built.symm

private theorem checkPathsForOrder_sound
    {n : Nat} {base : CaseData} {records : Array Record}
    {paths : List (List Nat)} {recordIndex checked : Nat}
    (accepted :
      checkPathsForOrder n base records paths recordIndex = .ok checked) :
    ∀ path ∈ paths,
      ∃ record : Record,
        ValidFor { base with equality := Model.pathEquality n path } record := by
  induction paths generalizing recordIndex checked with
  | nil =>
      intro path hpath
      simp at hpath
  | cons first remaining ih =>
      cases hvalid : Model.validOptimalPath n first with
      | false =>
          simp [checkPathsForOrder, hvalid] at accepted
          change Except.error _ = Except.ok checked at accepted
          cases accepted
      | true =>
          cases hrecord : records[recordIndex]? with
          | none =>
              simp [checkPathsForOrder, hvalid, hrecord]
                at accepted
          | some record =>
              cases hcheck : checkRecord
                  { base with equality := Model.pathEquality n first }
                  record with
              | error message =>
                  simp [checkPathsForOrder, hvalid, hrecord, hcheck]
                    at accepted
              | ok value =>
                  cases value
                  have hremaining :
                      checkPathsForOrder n base records remaining
                        (recordIndex + 1) = .ok checked := by
                    simpa [checkPathsForOrder, hvalid, hrecord, hcheck,
                      Except.bind]
                      using accepted
                  intro path hpath
                  rcases List.mem_cons.mp hpath with rfl | htail
                  · exact ⟨record, checkRecord_sound hcheck⟩
                  · exact ih hremaining path htail

private theorem checkOrders_sound
    {n : Nat} {paths : List (List Nat)} {records : Array Record}
    {orders : List (List Model.Edge)} {recordIndex checked : Nat}
    (accepted :
      checkOrders n paths records orders recordIndex = .ok checked) :
    ∀ order ∈ orders,
      ∀ path ∈ paths,
        ∃ record : Record,
          ValidFor (Model.buildCaseData n order path) record := by
  induction orders generalizing recordIndex checked with
  | nil =>
      intro order horder
      simp at horder
  | cons firstOrder remainingOrders ih =>
      cases hvalid : Model.validGreedyOrder n firstOrder with
      | false =>
          simp [checkOrders, hvalid] at accepted
          change Except.error _ = Except.ok checked at accepted
          cases accepted
      | true =>
          cases paths with
          | nil =>
              simp [checkOrders, hvalid] at accepted
              change Except.error _ = Except.ok checked at accepted
              cases accepted
          | cons firstPath remainingPaths =>
              cases hbase : Model.buildCaseData? n firstOrder firstPath with
              | none =>
                  simp [checkOrders, hvalid, hbase] at accepted
              | some base =>
                  cases hpaths : checkPathsForOrder n base records
                      (firstPath :: remainingPaths) recordIndex with
                  | error message =>
                      simp [checkOrders, hvalid, hbase, hpaths]
                        at accepted
                      change Except.error _ = Except.ok checked at accepted
                      cases accepted
                  | ok nextIndex =>
                      have hremaining :
                          checkOrders n (firstPath :: remainingPaths) records
                            remainingOrders nextIndex = .ok checked := by
                        simp [checkOrders, hvalid, hbase, hpaths] at accepted
                        change checkOrders n (firstPath :: remainingPaths)
                          records remainingOrders nextIndex = .ok checked
                          at accepted
                        exact accepted
                      have hpathsSound := checkPathsForOrder_sound hpaths
                      have hbaseEq := buildCaseData?_eq_some hbase
                      intro order horder path hpath
                      rcases List.mem_cons.mp horder with rfl | htail
                      · rcases hpathsSound path hpath with ⟨record, valid⟩
                        refine ⟨record, ?_⟩
                        rw [hbaseEq] at valid
                        exact valid
                      · exact ih hremaining order htail path hpath

/-- Successful positional replay certifies every chronology/path pair in the
supplied enumeration.  The conclusion intentionally forgets record indices;
the executable traversal still enforces their exact row-major order. -/
theorem checkPositionalCases_sound
    {n : Nat} {orders : List (List Model.Edge)}
    {paths : List (List Nat)} {records : Array Record} {checked : Nat}
    (accepted :
      checkPositionalCases n orders paths records = .ok checked) :
    ∀ order ∈ orders,
      ∀ path ∈ paths,
        ∃ record : Record,
          ValidFor (Model.buildCaseData n order path) record := by
  by_cases hsize : records.size ≠ orders.length * paths.length
  · simp [checkPositionalCases, hsize] at accepted
    change Except.error _ = Except.ok checked at accepted
    cases accepted
  · cases horders : checkOrders n paths records orders 0 with
    | error message =>
        simp [checkPositionalCases, hsize, horders] at accepted
        change Except.error _ = Except.ok checked at accepted
        cases accepted
    | ok traversed =>
        exact checkOrders_sound horders

/-- The exact 60-order stream used by the six-input corpus. -/
def sixRepresentativeOrders : List (List Model.Edge) :=
  Model.representativeGreedyOrders 6

/-- Check that the stored representative rule gives two disjoint 60-order
halves covering every six-input greedy chronology under the involution. -/
def sixSymmetryCoverageValid : Bool :=
  let allOrders := Model.greedyEdgeOrders 6
  let representatives := sixRepresentativeOrders
  let images := representatives.map (Model.reverseRelabelOrder 6)
  allOrders.length == 120 &&
    representatives.length == 60 &&
    allOrders.eraseDups.length == allOrders.length &&
    representatives.eraseDups.length == representatives.length &&
    images.eraseDups.length == images.length &&
    allOrders.all (fun order =>
      Model.reverseRelabelOrder 6 (Model.reverseRelabelOrder 6 order) == order) &&
    representatives.all (fun order => !(images.contains order)) &&
    allOrders.all (fun order =>
      representatives.contains order || images.contains order) &&
    images.all allOrders.contains

private def reverseRelabelVariable (n : Nat) : Model.Variable → Model.Variable
  | .length vertex => .length (Model.reverseLabel n vertex)
  | .overlap edge => .overlap (Model.reverseRelabelEdge n edge)


/-- The 120 six-input chronologies are kernel-checked to split into the
advertised 60 disjoint involution orbits. -/
theorem sixSymmetryCoverageValid_eq_true :
    sixSymmetryCoverageValid = true := by
  set_option maxRecDepth 100000 in
    decide

/-- The finite chronology/path enumeration sizes used by both corpora are
ordinary kernel reductions, independent of the native replay. -/
theorem caseEnumerationCounts :
    (Model.greedyEdgeOrders 5).length = 24 ∧
    (Model.optimalPaths 5).length = 120 ∧
    (Model.greedyEdgeOrders 6).length = 120 ∧
    sixRepresentativeOrders.length = 60 ∧
    (Model.optimalPaths 6).length = 720 := by
  set_option maxRecDepth 100000 in
    decide

/-- Coordinate `j` contains the old-system coordinate occupied by new
coordinate `j` under reverse-and-relabel. -/
def symmetryCoordinateMap? (n : Nat) : Option (Array Nat) := do
  let coordinates ← (Model.allVariables n).mapM fun coordinate =>
    Model.variableIndex? n (reverseRelabelVariable n coordinate)
  pure coordinates.toArray

private def natAt (values : Array Nat) (index : Nat) : Nat :=
  values[index]?.getD values.size

private def symmetryCoordinateMapValid (n : Nat) (mapping : Array Nat) : Bool :=
  let variableCount := Model.variableCount n
  mapping.size == variableCount &&
    mapping.all (fun index => decide (index < variableCount)) &&
    mapping.toList.eraseDups.length == mapping.size &&
    (List.range variableCount).all (fun index =>
      natAt mapping (natAt mapping index) == index)

/-- Transport a new-system coefficient vector into old-system coordinates. -/
def mapNewCoefficientsToOld (mapping : Array Nat)
    (coefficients : Array Int) : Array Int :=
  (List.range mapping.size).foldl
    (init := Array.replicate mapping.size 0) fun result newIndex =>
      result.setIfInBounds (natAt mapping newIndex) (intAt coefficients newIndex)

private abbrev RowKey := Array Int × Int

private def rowSystem (data : CaseData) : List RowKey :=
  (List.range data.rows.size).map fun rowIndex =>
    (data.rows[rowIndex]?.getD #[], intAt data.rhs rowIndex)

private def mappedRowSystem (mapping : Array Nat)
    (data : CaseData) : List RowKey :=
  (rowSystem data).map fun row =>
    (mapNewCoefficientsToOld mapping row.1, row.2)

private def compareIntLists : List Int → List Int → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: lefts, right :: rights =>
      match compare left right with
      | .eq => compareIntLists lefts rights
      | ordering => ordering

private def rowKeyLE (left right : RowKey) : Bool :=
  match compareIntLists left.1.toList right.1.toList with
  | .lt => true
  | .gt => false
  | .eq => decide (left.2 ≤ right.2)

private def rowSystemsMatch (mapping : Array Nat)
    (oldData newData : CaseData) : Bool :=
  dimensionsValidBool oldData && dimensionsValidBool newData &&
    oldData.rows.size == oldData.rhs.size &&
    newData.rows.size == newData.rhs.size &&
    oldData.rows.size == newData.rows.size &&
    (rowSystem oldData).mergeSort rowKeyLE ==
      (mappedRowSystem mapping newData).mergeSort rowKeyLE

/-- Executable replay of the full LP isomorphism used to halve the six-input
corpus: coordinate involution, row/RHS multisets for all 60 order pairs,
objective invariance, and every reflected optimum-path equality. -/
def sixSymmetryInvariantValid : Bool :=
  match symmetryCoordinateMap? 6 with
  | none => false
  | some mapping =>
      let probePath := Model.vertices 6
      let objective := Model.greedyObjective 6
      let orderSystemsMatch := sixRepresentativeOrders.all fun order =>
        let reflectedOrder := Model.reverseRelabelOrder 6 order
        let oldData := Model.buildCaseData 6 order probePath
        let newData := Model.buildCaseData 6 reflectedOrder probePath
        rowSystemsMatch mapping oldData newData
      let pathsMatch := (Model.optimalPaths 6).all fun path =>
        let reflectedPath := Model.reverseRelabelPath 6 path
        Model.reverseRelabelPath 6 reflectedPath == path &&
          mapNewCoefficientsToOld mapping
              (Model.pathEquality 6 reflectedPath) ==
            Model.pathEquality 6 path
      sixSymmetryCoverageValid &&
        symmetryCoordinateMapValid 6 mapping &&
        mapNewCoefficientsToOld mapping objective == objective &&
        orderSystemsMatch && pathsMatch

/-- Replay the complete five-input corpus in Python permutation order. -/
def checkFiveCorpus (header : Certificate.Header)
    (records : Array Record) : Except String Nat := do
  let orders := Model.greedyEdgeOrders 5
  let paths := Model.optimalPaths 5
  if orders.length ≠ 24 || paths.length ≠ 120 then
    throw "five-input permutation enumeration has unexpected dimensions"
  validateHeader header records "five" 5 2880 fiveSourceSha256
  checkPositionalCases 5 orders paths records

/-- Successful replay of the complete five-input corpus supplies a valid
record for every case in the exact executable chronology/path product.

This is definitionally the `CertificateCoverage 5` proposition used by the
higher-level corpus bridge, stated here to avoid a dependency cycle. -/
theorem checkFiveCorpus_coverage_sound
    {header : Certificate.Header} {records : Array Record}
    (accepted : checkFiveCorpus header records = .ok 2880) :
    ∀ chronology ∈ Model.greedyEdgeOrders 5,
      ∀ path ∈ Model.optimalPaths 5,
        ∃ record : Record,
          ValidFor (Model.buildCaseData 5 chronology path) record := by
  have horders : (Model.greedyEdgeOrders 5).length = 24 :=
    caseEnumerationCounts.1
  have hpaths : (Model.optimalPaths 5).length = 120 :=
    caseEnumerationCounts.2.1
  unfold checkFiveCorpus at accepted
  simp [horders, hpaths] at accepted
  cases hheader : validateHeader header records "five" 5 2880
      fiveSourceSha256 with
  | error message =>
      simp [hheader] at accepted
      change Except.error _ = Except.ok 2880 at accepted
      cases accepted
  | ok value =>
      cases value
      have positional :
          checkPositionalCases 5 (Model.greedyEdgeOrders 5)
            (Model.optimalPaths 5) records = .ok 2880 := by
        simp [hheader] at accepted
        change checkPositionalCases 5 (Model.greedyEdgeOrders 5)
          (Model.optimalPaths 5) records = .ok 2880 at accepted
        exact accepted
      exact checkPositionalCases_sound positional

/-- Replay the complete six-input representative corpus in Python order. -/
def checkSixCorpus (header : Certificate.Header)
    (records : Array Record) : Except String Nat := do
  let paths := Model.optimalPaths 6
  if !sixSymmetryInvariantValid then
    throw "six-input reverse/relabel LP isomorphism replay failed"
  if sixRepresentativeOrders.length ≠ 60 || paths.length ≠ 720 then
    throw "six-input permutation enumeration has unexpected dimensions"
  validateHeader header records "six" 6 43200 sixSourceSha256
  checkPositionalCases 6 sixRepresentativeOrders paths records

def checkFiveFile (path : System.FilePath) : IO (Except String Nat) := do
  let loaded ← Certificate.load path
  pure <| match loaded with
    | .error message => .error message
    | .ok (header, records) => checkFiveCorpus header records

def checkSixFile (path : System.FilePath) : IO (Except String Nat) := do
  let loaded ← Certificate.load path
  pure <| match loaded with
    | .error message => .error message
    | .ok (header, records) => checkSixCorpus header records

/-- Load and replay both exact corpora. -/
def checkAllFiles (fivePath sixPath : System.FilePath) :
    IO (Except String (Nat × Nat)) := do
  match ← checkFiveFile fivePath with
  | .error message => pure (.error s!"five-input corpus: {message}")
  | .ok fiveCount =>
      match ← checkSixFile sixPath with
      | .error message => pure (.error s!"six-input corpus: {message}")
      | .ok sixCount => pure (.ok (fiveCount, sixCount))

/-- Replay the checked-in compact corpora from the repository root. -/
def checkDefaultFiles : IO (Except String (Nat × Nat)) :=
  checkAllFiles "Lean/Data/five.cert" "Lean/Data/six.cert"

end GreedySuperstring.Checker
