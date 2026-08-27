import GreedySuperstring.ChronologyConstruction

/-!
# Semantic orders in the executable case enumeration

This module proves completeness of `Model.permutations` directly from its
custom `eraseIdx` recursion, then connects semantic Hamiltonian orders and
canonical labelled greedy runs to the exact executable case lists.
-/

namespace GreedySuperstring

open GreedySuperstring.Relaxation
open ChronologyBridge

namespace EnumerationBridge

/-! ## Completeness of the executable permutation generator -/

/-- Every permutation of `values` is emitted by the custom recursive
generator at the candidate's full length. -/
theorem mem_permutationsOfLength_of_perm
    {β : Type u} {candidate values : List β}
    (permuted : candidate.Perm values) :
    candidate ∈ Model.permutationsOfLength candidate.length values := by
  induction candidate generalizing values with
  | nil =>
      have hvalues : values = [] := permuted.nil_eq.symm
      subst values
      simp [Model.permutationsOfLength]
  | cons head tail ih =>
      have hhead : head ∈ values :=
        permuted.mem_iff.mp (by simp)
      rcases List.mem_iff_getElem.mp hhead with
        ⟨index, hindex, hvalue⟩
      have hselected :
          (head :: values.eraseIdx index).Perm values := by
        simpa [hvalue] using List.getElem_cons_eraseIdx_perm hindex
      have htail : tail.Perm (values.eraseIdx index) :=
        (permuted.trans hselected.symm).cons_inv
      simp only [List.length_cons, Model.permutationsOfLength,
        List.mem_flatMap]
      refine ⟨index, List.mem_range.mpr hindex, ?_⟩
      rw [List.getElem?_eq_getElem hindex]
      simp only [List.mem_map]
      exact ⟨tail, ih htail, by simp [hvalue]⟩

/-- Every full-list permutation occurs in `Model.permutations`; ordering and
multiplicity of the executable list remain exactly those of the Model code. -/
theorem mem_permutations_of_perm
    {β : Type u} {candidate values : List β}
    (permuted : candidate.Perm values) :
    candidate ∈ Model.permutations values := by
  have emitted := mem_permutationsOfLength_of_perm permuted
  simpa [Model.permutations, permuted.length_eq] using emitted

/-! ## Semantic optimum paths -/

private theorem ofFn_val_eq_vertices (n : Nat) :
    (List.ofFn fun i : Fin n => i.val) = Model.vertices n := by
  unfold Model.vertices
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp

/-- The natural-number label list of every semantic Hamiltonian order is
present in the executable optimum-path enumeration. -/
theorem optimalPathLabels_mem_optimalPaths
    {n : Nat} (order : HamiltonianOrder n) :
    PrimalBridge.optimalPathLabels order ∈ Model.optimalPaths n := by
  unfold Model.optimalPaths
  apply mem_permutations_of_perm
  have mapped := order.perm.map Fin.val
  simpa [PrimalBridge.optimalPathLabels, List.map_ofFn,
    Function.comp_def, ofFn_val_eq_vertices] using mapped

/-! ## Semantic greedy chronologies -/

/-- A canonical terminal path forces the chronology of any labelled run to
occur in the executable greedy-edge-order enumeration.  Chronological merge
edges may be in any order; their multiset is the terminal path's adjacency
list by `edges_perm_adjacentEdges`. -/
theorem modelChronology_mem_greedyEdgeOrders
    {α : Type u} {n : Nat} [DecidableEq α]
    {data : WordInstance α n}
    {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    (canonical : CanonicalTerminalPath terminal) :
    modelChronology edges ∈ Model.greedyEdgeOrders n := by
  unfold Model.greedyEdgeOrders
  apply mem_permutations_of_perm
  have mapped := run.edges_perm_adjacentEdges.map modelEdge
  have chronologyPerm :
      (modelChronology edges).Perm
        ((adjacentEdges terminal.labels).map modelEdge) := by
    simpa [modelChronology] using mapped
  rw [canonical] at chronologyPerm
  exact chronologyPerm

/-- Every edge in the executable chronology of a canonical labelled run is
a valid off-diagonal edge on `Fin n`.  This is the exact well-formedness
premise consumed by the dense-encoding constructor. -/
theorem modelChronology_edges_valid
    {α : Type u} {n : Nat} [DecidableEq α]
    {data : WordInstance α n}
    {terminal : PathComponent (Fin n) α}
    {edges : List (Fin n × Fin n)}
    (run : LabelledGreedyRun data.overlap
      (initialComponents data.word (List.ofFn id)) [terminal] edges)
    (canonical : CanonicalTerminalPath terminal) :
    ∀ edge ∈ modelChronology edges,
      PrimalBridge.EdgeValid n edge := by
  have mapped := run.edges_perm_adjacentEdges.map modelEdge
  have chronologyPerm :
      (modelChronology edges).Perm
        ((adjacentEdges terminal.labels).map modelEdge) := by
    simpa [modelChronology] using mapped
  rw [canonical] at chronologyPerm
  intro edge hedge
  have hcanonical : edge ∈ Model.greedyPathEdges n :=
    chronologyPerm.mem_iff.mp hedge
  rcases List.mem_map.mp hcanonical with ⟨index, hindex, rfl⟩
  have hindexLt := List.mem_range.mp hindex
  change index < n ∧ index + 1 < n ∧ index ≠ index + 1
  omega

end EnumerationBridge

end GreedySuperstring
