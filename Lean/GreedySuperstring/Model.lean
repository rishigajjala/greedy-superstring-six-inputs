import Batteries

/-!
# Executable finite LP model

This file is a direct, n-parameter port of the deterministic row builders in
five_string_lp_model.py and generalize/six_string_lp_model.py.

The coefficient order is part of the public format. Length variables come
first, in vertex order. They are followed by directed-overlap variables in
lexicographic (source, target) order, omitting loops. Inequalities are emitted
as endpoint caps, directed triangles, unordered-pair rows, and then the
stepwise greedy-dominance and licensed conditional-rectangle rows.

All arithmetic data are integral. A right-hand side of one denotes one copy
of the homogeneous optimum parameter; every other inequality RHS is zero.
-/

namespace GreedySuperstring.Model

/-- A directed edge between original string labels. -/
structure Edge where
  src : Nat
  dst : Nat
deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Symbolic names for the dense LP coordinates. -/
inductive Variable where
  | length (vertex : Nat)
  | overlap (edge : Edge)
deriving DecidableEq, BEq, Repr

/-- A tag recording which deterministic row-family emitted an inequality. -/
inductive RowKind where
  | endpointCap (edge : Edge) (endpoint : Nat)
  | triangle (i j k : Nat)
  | intervalPair (i j : Nat)
  | greedyDominance (step : Nat) (selected candidate : Edge)
  | licensedRectangle (step : Nat) (selected crossA crossB bottom : Edge)
deriving DecidableEq, BEq, Repr

abbrev Coefficients := Array Int

/-- One inequality coefficients · x ≤ rhs · OPT. -/
structure Row where
  coefficients : Coefficients
  rhs : Int
  kind : RowKind
deriving DecidableEq, BEq, Repr

/-- The complete deterministic data for one chronology/optimal-path case. -/
structure CaseModel where
  n : Nat
  greedyOrder : List Edge
  optimalPath : List Nat
  rows : Array Row
  equality : Coefficients
  objective : Coefficients
deriving DecidableEq, BEq, Repr

/-- Checker-facing dense LP data, with row tags and case metadata erased. -/
structure CaseData where
  rows : Array (Array Int)
  rhs : Array Int
  equality : Array Int
  objective : Array Int
  nLengths : Nat
deriving DecidableEq, BEq, Repr

/-- Vertices in the same order as Python's range(n). -/
def vertices (n : Nat) : List Nat := List.range n

/-- All non-loop directed edges in Python tuple-comprehension order. -/
def directedEdges (n : Nat) : List Edge :=
  (vertices n).flatMap fun i =>
    (vertices n).filterMap fun j =>
      if i == j then none else some { src := i, dst := j }

/-- Number of length and directed-overlap coordinates. -/
def variableCount (n : Nat) : Nat := n + n * (n - 1)

/-- Dense coordinate occupied by a valid directed edge. -/
def overlapIndex (n : Nat) (edge : Edge) : Nat :=
  n + edge.src * (n - 1) +
    (if edge.dst < edge.src then edge.dst else edge.dst - 1)

/-- Checked conversion of a symbolic variable to its dense coordinate. -/
def variableIndex? (n : Nat) : Variable → Option Nat
  | .length i => if i < n then some i else none
  | .overlap edge =>
      if edge.src < n ∧ edge.dst < n ∧ edge.src ≠ edge.dst then
        some (overlapIndex n edge)
      else
        none

/-- Symbolic variables in exact dense-coordinate order. -/
def allVariables (n : Nat) : List Variable :=
  (vertices n).map Variable.length ++
    (directedEdges n).map Variable.overlap

/-- Safe coefficient lookup; malformed external indices read as zero. -/
def coefficientAt (coefficients : Coefficients) (index : Nat) : Int :=
  coefficients[index]?.getD 0

/-- Add to one dense coefficient, leaving an out-of-range array unchanged. -/
def addCoefficient (coefficients : Coefficients) (index : Nat)
    (delta : Int) : Coefficients :=
  coefficients.setIfInBounds index (coefficientAt coefficients index + delta)

private def coefficientsFromTerms (n : Nat)
    (terms : List (Variable × Int)) : Coefficients :=
  terms.foldl
    (fun coefficients term =>
      match variableIndex? n term.1 with
      | none => coefficients
      | some index => addCoefficient coefficients index term.2)
    (Array.replicate (variableCount n) 0)

private def makeRow (n : Nat) (rhs : Int) (kind : RowKind)
    (terms : List (Variable × Int)) : Row :=
  { coefficients := coefficientsFromTerms n terms
    rhs := rhs
    kind := kind }

/-- The fixed relabeled greedy path 0 → 1 → ... → n-1. -/
def greedyPathEdges (n : Nat) : List Edge :=
  (List.range (n - 1)).map fun i => { src := i, dst := i + 1 }

/-- Consecutive directed edges of a proposed vertex path. -/
def pathEdges (path : List Nat) : List Edge :=
  (path.zip path.tail).map fun pair => { src := pair.1, dst := pair.2 }

/-- Undirected adjacency in the weak graph of already selected edges. -/
def weaklyAdjacent (chosen : List Edge) (u v : Nat) : Bool :=
  chosen.any fun edge =>
    ((edge.src == u) && (edge.dst == v)) ||
      ((edge.src == v) && (edge.dst == u))

private def closureStep (n : Nat) (chosen : List Edge)
    (seen : List Nat) : List Nat :=
  (vertices n).filter fun v =>
    seen.contains v || seen.any fun u => weaklyAdjacent chosen u v

/-- Weak component of start, computed by n deterministic closure rounds. -/
def weakComponent (n : Nat) (chosen : List Edge) (start : Nat) : List Nat :=
  (vertices n).foldl (fun seen _ => closureStep n chosen seen) [start]

/-- Whether two labels lie in the same weak component of chosen. -/
def weaklyConnected (n : Nat) (chosen : List Edge) (u v : Nat) : Bool :=
  (weakComponent n chosen u).contains v

/-- Executable valid-edge predicate for the complete directed graph. -/
def validEdge (n : Nat) (edge : Edge) : Bool :=
  decide (edge.src < n) && decide (edge.dst < n) && !(edge.src == edge.dst)

/-- Exact path-forest feasibility predicate used by both Python builders. -/
def feasibleEdge (n : Nat) (chosen : List Edge) (edge : Edge) : Bool :=
  validEdge n edge &&
    !(chosen.any fun old => old.src == edge.src) &&
    !(chosen.any fun old => old.dst == edge.dst) &&
    !(weaklyConnected n chosen edge.src edge.dst)

/-- Feasible original-label edges, in deterministic directed-edge order. -/
def feasibleEdges (n : Nat) (chosen : List Edge) : List Edge :=
  (directedEdges n).filter (feasibleEdge n chosen)

private def chronologyValidAux (n : Nat) (chosen : List Edge) :
    List Edge → Bool
  | [] => true
  | selected :: remaining =>
      feasibleEdge n chosen selected &&
        chronologyValidAux n (chosen ++ [selected]) remaining

/-- A list of edges builds a directed path forest in the displayed order. -/
def pathForest (n : Nat) (edges : List Edge) : Bool :=
  chronologyValidAux n [] edges

/-- The selected chronology passes the path-forest feasibility test. -/
def chronologyValid (n : Nat) (order : List Edge) : Bool :=
  pathForest n order

/-- Endpoint-cap rows wᵢⱼ ≤ lᵢ and wᵢⱼ ≤ lⱼ. -/
def endpointCapRows (n : Nat) : List Row :=
  (directedEdges n).flatMap fun edge =>
    [edge.src, edge.dst].map fun endpoint =>
      makeRow n 0 (.endpointCap edge endpoint)
        [(.overlap edge, 1), (.length endpoint, -1)]

/-- Directed overlap-distance triangles, in permutation order. -/
def triangleRows (n : Nat) : List Row :=
  (vertices n).flatMap fun i =>
    (vertices n).flatMap fun j =>
      (vertices n).filterMap fun k =>
        if i ≠ j ∧ i ≠ k ∧ j ≠ k then
          let ij : Edge := { src := i, dst := j }
          let jk : Edge := { src := j, dst := k }
          let ik : Edge := { src := i, dst := k }
          some <| makeRow n 0 (.triangle i j k)
            [(.overlap ij, 1), (.overlap jk, 1),
              (.overlap ik, -1), (.length j, -1)]
        else
          none

/-- Global unordered-pair rows lᵢ+lⱼ-wᵢⱼ-wⱼᵢ ≤ OPT. -/
def intervalPairRows (n : Nat) : List Row :=
  (vertices n).flatMap fun i =>
    (vertices n).filterMap fun j =>
      if i < j then
        let ij : Edge := { src := i, dst := j }
        let ji : Edge := { src := j, dst := i }
        some <| makeRow n 1 (.intervalPair i j)
          [(.length i, 1), (.length j, 1),
            (.overlap ij, -1), (.overlap ji, -1)]
      else
        none

/-- Greedy-dominance rows for one step, in feasible-edge order. -/
def greedyDominanceRows (n step : Nat) (selected : Edge)
    (feasible : List Edge) : List Row :=
  (feasible.filter fun candidate => !(candidate == selected)).map fun candidate =>
    makeRow n 0 (.greedyDominance step selected candidate)
      [(.overlap candidate, 1), (.overlap selected, -1)]

private def hasLoop (edge : Edge) : Bool := edge.src == edge.dst

/-- Every licensed conditional-Monge rectangle at one chronology step.

Only the two cross edges must be feasible. As in the Python model, the bottom
edge need not be feasible, and repeated terms are accumulated, not overwritten.
-/
def licensedRectangleRows (n step : Nat) (selected : Edge)
    (feasible : List Edge) : List Row :=
  (vertices n).flatMap fun uPrime =>
    (vertices n).filterMap fun vPrime =>
      let crossA : Edge := { src := selected.src, dst := vPrime }
      let crossB : Edge := { src := uPrime, dst := selected.dst }
      let bottom : Edge := { src := uPrime, dst := vPrime }
      if hasLoop selected || hasLoop crossA || hasLoop crossB || hasLoop bottom then
        none
      else if feasible.contains crossA && feasible.contains crossB then
        some <| makeRow n 0
          (.licensedRectangle step selected crossA crossB bottom)
          [(.overlap crossA, 1), (.overlap crossB, 1),
            (.overlap selected, -1), (.overlap bottom, -1)]
      else
        none

private def greedyRowsAux (n : Nat) (chosen : List Edge) (step : Nat) :
    List Edge → List Row
  | [] => []
  | selected :: remaining =>
      let feasible := feasibleEdges n chosen
      greedyDominanceRows n step selected feasible ++
        licensedRectangleRows n step selected feasible ++
        greedyRowsAux n (chosen ++ [selected]) (step + 1) remaining

/-- All chronology-dependent rows. -/
def greedyRows (n : Nat) (order : List Edge) : List Row :=
  greedyRowsAux n [] 0 order


/-- Public recursion view of chronology-dependent row generation.

This wrapper is definitionally the private executable worker.  Its equations
are a theorem-facing induction API and do not change row order or contents. -/
def greedyRowsFrom (n : Nat) (chosen : List Edge) (step : Nat)
    (order : List Edge) : List Row :=
  greedyRowsAux n chosen step order

@[simp] theorem greedyRowsFrom_nil (n : Nat) (chosen : List Edge)
    (step : Nat) :
    greedyRowsFrom n chosen step [] = [] := rfl

@[simp] theorem greedyRowsFrom_cons (n : Nat) (chosen : List Edge)
    (step : Nat) (selected : Edge) (remaining : List Edge) :
    greedyRowsFrom n chosen step (selected :: remaining) =
      let feasible := feasibleEdges n chosen
      greedyDominanceRows n step selected feasible ++
        licensedRectangleRows n step selected feasible ++
        greedyRowsFrom n (chosen ++ [selected]) (step + 1) remaining := rfl

theorem greedyRows_eq_from (n : Nat) (order : List Edge) :
    greedyRows n order = greedyRowsFrom n [] 0 order := rfl


/-- Full inequality system in exact Python family order. -/
def inequalityRows (n : Nat) (order : List Edge) : List Row :=
  endpointCapRows n ++ triangleRows n ++ intervalPairRows n ++
    greedyRows n order

/-- The nominated optimum-path equality. -/
def pathEquality (n : Nat) (path : List Nat) : Coefficients :=
  coefficientsFromTerms n <|
    (vertices n).map (fun i => (.length i, 1)) ++
      (pathEdges path).map (fun edge => (.overlap edge, -1))

/-- Objective equal to minus the relabeled GREEDY output length. -/
def greedyObjective (n : Nat) : Coefficients :=
  coefficientsFromTerms n <|
    (vertices n).map (fun i => (.length i, -1)) ++
      (greedyPathEdges n).map (fun edge => (.overlap edge, 1))

/-- Build data without validating membership in the enumerated case family. -/
def buildCaseUnchecked (n : Nat) (order : List Edge)
    (path : List Nat) : CaseModel :=
  { n := n
    greedyOrder := order
    optimalPath := path
    rows := (inequalityRows n order).toArray
    equality := pathEquality n path
    objective := greedyObjective n }

/-- Boolean test that path is a permutation of 0,...,n-1. -/
def validOptimalPath (n : Nat) (path : List Nat) : Bool :=
  path.length == n &&
    path.all (fun i => decide (i < n)) &&
    path.eraseDups.length == n

/-- Boolean test that order is a permutation of the canonical greedy edges. -/
def validGreedyOrder (n : Nat) (order : List Edge) : Bool :=
  let canonical := greedyPathEdges n
  order.length == canonical.length &&
    order.all canonical.contains &&
    order.eraseDups.length == canonical.length &&
    chronologyValid n order

/-- Validate public case metadata before building its dense LP data. -/
def validCaseInput (n : Nat) (order : List Edge) (path : List Nat) : Bool :=
  validGreedyOrder n order && validOptimalPath n path

/-- Checked builder for the finite case family. -/
def buildCase? (n : Nat) (order : List Edge)
    (path : List Nat) : Option CaseModel :=
  if validCaseInput n order path then
    some (buildCaseUnchecked n order path)
  else
    none

/-- Dense inequality matrix, convenient for certificate checkers. -/
def CaseModel.matrix (model : CaseModel) : Array Coefficients :=
  model.rows.map Row.coefficients

/-- Dense inequality right-hand sides, convenient for certificate checkers. -/
def CaseModel.rightHandSides (model : CaseModel) : Array Int :=
  model.rows.map Row.rhs

/-- Erase diagnostic tags and metadata to obtain the certificate-checker API. -/
def CaseModel.toCaseData (model : CaseModel) : CaseData :=
  { rows := model.matrix
    rhs := model.rightHandSides
    equality := model.equality
    objective := model.objective
    nLengths := model.n }

/-- Unchecked dense builder for certificate data. -/
def buildCaseData (n : Nat) (order : List Edge) (path : List Nat) : CaseData :=
  (buildCaseUnchecked n order path).toCaseData

/-- Checked dense builder for certificate data. -/
def buildCaseData? (n : Nat) (order : List Edge)
    (path : List Nat) : Option CaseData :=
  (buildCase? n order path).map CaseModel.toCaseData

/-- Deterministic k-permutations in Python itertools.permutations order. -/
def permutationsOfLength {α : Type u} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, values =>
      (List.range values.length).flatMap fun index =>
        match values[index]? with
        | none => []
        | some value =>
            (permutationsOfLength k (values.eraseIdx index)).map
              fun rest => value :: rest

/-- Full-length permutations in Python itertools.permutations order. -/
def permutations {α : Type u} (values : List α) : List (List α) :=
  permutationsOfLength values.length values

/-- All canonical greedy-edge chronologies in certificate order. -/
def greedyEdgeOrders (n : Nat) : List (List Edge) :=
  permutations (greedyPathEdges n)

/-- All nominated optimum paths in certificate order. -/
def optimalPaths (n : Nat) : List (List Nat) :=
  permutations (vertices n)

/-- Reverse a label under the involution i ↦ n-1-i. -/
def reverseLabel (n i : Nat) : Nat := n - 1 - i

/-- Reverse both string direction and labels while preserving the canonical
greedy path as an unoriented symmetry. -/
def reverseRelabelEdge (n : Nat) (edge : Edge) : Edge :=
  { src := reverseLabel n edge.dst
    dst := reverseLabel n edge.src }

/-- Apply reverse-and-relabel to every edge of a chronology. -/
def reverseRelabelOrder (n : Nat) (order : List Edge) : List Edge :=
  order.map (reverseRelabelEdge n)

/-- Reverse an optimum path and complement every vertex label. -/
def reverseRelabelPath (n : Nat) (path : List Nat) : List Nat :=
  path.reverse.map (reverseLabel n)

/-- Lexicographic edge comparison matching Python tuple comparison. -/
def edgeLexLess (left right : Edge) : Bool :=
  if left.src < right.src then true
  else if right.src < left.src then false
  else decide (left.dst < right.dst)

/-- Lexicographic chronology comparison matching Python tuple comparison. -/
def orderLexLess : List Edge → List Edge → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: lefts, right :: rights =>
      if left == right then orderLexLess lefts rights
      else edgeLexLess left right

/-- One lexicographically smaller chronology from each reverse/relabel orbit.
For n=6 this is the 60-order stream used by the certificate corpus. -/
def representativeGreedyOrders (n : Nat) : List (List Edge) :=
  (greedyEdgeOrders n).filter fun order =>
    orderLexLess order (reverseRelabelOrder n order)

end GreedySuperstring.Model
