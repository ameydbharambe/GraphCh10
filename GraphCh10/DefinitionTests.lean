import GraphCh10.Definitions

/-!
# Sanity tests for `GraphCh10.Definitions` (Phase 1)

Each definition gets a small positive test and at least one edge-case test, as listed in the
approved design. All checks are kernel-checked with `decide`, `rfl` or `simp`
(no compiled evaluation).
-/

namespace GraphCh10.Tests

open GraphCh10

/-! ## Test graphs -/

/-- One vertex with a single loop. -/
def loop1 : UGraph (Fin 1) (Fin 1) := ⟨fun _ => s(0, 0)⟩

/-- Two vertices joined by two parallel edges. -/
def dbl : UGraph (Fin 2) (Fin 2) := ⟨fun _ => s(0, 1)⟩

/-- The path 0 – 1 – 2. -/
def p3 : UGraph (Fin 3) (Fin 2) := ⟨fun e => if e = 0 then s(0, 1) else s(1, 2)⟩

/-- Two isolated vertices. -/
def two0 : UGraph (Fin 2) Empty := ⟨Empty.elim⟩

/-- The graph with no vertices and no edges. -/
def empty0 : UGraph (Fin 0) Empty := ⟨Empty.elim⟩

/-- The Supp. 8 counterexample shape: edges {0,1}, {1,2}, {1,2}. -/
def ex8 : UGraph (Fin 3) (Fin 3) := ⟨fun e => if e = 0 then s(0, 1) else s(1, 2)⟩

/-- A single directed edge (0, 1). -/
def arc : DGraph (Fin 2) (Fin 1) := ⟨fun _ => (0, 1)⟩

/-- Directed edges (0, 1) and (1, 0). -/
def both : DGraph (Fin 2) (Fin 2) := ⟨fun e => if e = 0 then (0, 1) else (1, 0)⟩

/-- Two copies of the directed edge (0, 1). -/
def dup : DGraph (Fin 2) (Fin 2) := ⟨fun _ => (0, 1)⟩

/-- One vertex with a directed loop (0, 0). -/
def dloop : DGraph (Fin 1) (Fin 1) := ⟨fun _ => (0, 0)⟩

/-- The directed 3-cycle (0,1), (1,2), (2,0). -/
def cyc3 : DGraph (Fin 3) (Fin 3) :=
  ⟨fun e => if e = 0 then (0, 1) else if e = 1 then (1, 2) else (2, 0)⟩

/-- The transitive tournament (0,1), (1,2), (0,2). -/
def tr3 : DGraph (Fin 3) (Fin 3) :=
  ⟨fun e => if e = 0 then (0, 1) else if e = 1 then (1, 2) else (0, 2)⟩

/-- One vertex, no edges. -/
def single : DGraph (Fin 1) Empty := ⟨Empty.elim⟩

/-! ## `UGraph` -/

example : p3.ends 0 = s(0, 1) := rfl
-- edge case: a graph with no vertices and no edges is a valid `UGraph`
example : UGraph (Fin 0) Empty := empty0

/-! ## `IsLoop` -/

example : loop1.IsLoop 0 := by unfold UGraph.IsLoop; decide
example : ¬ dbl.IsLoop 0 := by unfold UGraph.IsLoop; decide

/-! ## `IsMultigraph` -/

example : ex8.IsMultigraph := by unfold UGraph.IsMultigraph UGraph.IsLoop; decide
example : dbl.IsMultigraph := by unfold UGraph.IsMultigraph UGraph.IsLoop; decide
example : ¬ loop1.IsMultigraph := by unfold UGraph.IsMultigraph UGraph.IsLoop; decide

/-! ## `Adj` -/

example : p3.Adj 0 1 ∧ p3.Adj 1 0 := by decide
example : ¬ p3.Adj 0 2 := by decide
-- edge case: a loop makes a vertex adjacent to itself
example : loop1.Adj 0 0 := by decide

/-! ## `Incident` -/

example : p3.Incident 0 1 := by decide
example : ¬ p3.Incident 0 2 := by decide

/-! ## `deg` -/

example : p3.deg 1 = 2 := by decide
example : ex8.deg 0 = 1 ∧ ex8.deg 1 = 3 ∧ ex8.deg 2 = 2 := by decide
example : dbl.deg 0 = 2 := by decide
-- edge case: a loop is counted twice
example : loop1.deg 0 = 2 := by decide
-- edge case: an isolated vertex has degree zero
example : two0.deg 0 = 0 := by decide

/-! ## `nbhd` -/

example : p3.nbhd 1 = {0, 2} := by
  ext u
  change p3.Adj 1 u ↔ u = 0 ∨ u = 2
  revert u
  decide
-- edge case: a loop puts the vertex in its own neighborhood
example : loop1.nbhd 0 = {0} := by
  ext u
  change loop1.Adj 0 u ↔ u = 0
  revert u
  decide
-- edge case: an isolated vertex has empty neighborhood
example : two0.nbhd 0 = ∅ := by
  ext u
  change two0.Adj 0 u ↔ False
  revert u
  decide

/-! ## `nbhdSet` -/

example : p3.nbhdSet {0, 2} = {1} := by
  ext u
  change (∃ a, (a = 0 ∨ a = 2) ∧ p3.Adj a u) ↔ u = 1
  revert u
  decide
-- edge case: the neighborhood of the empty set is empty, in any graph
example {V E : Type} (G : UGraph V E) : G.nbhdSet ∅ = ∅ := by
  ext u
  simp [UGraph.nbhdSet]

/-! ## `DGraph` and `DAdj` -/

example : arc.ends 0 = (0, 1) := rfl
-- edge case: a directed loop is a valid `DGraph`
example : DGraph (Fin 1) (Fin 1) := dloop
example : arc.DAdj 0 1 := by decide
example : ¬ arc.DAdj 1 0 := by decide

/-! ## `inDeg`, `outDeg` -/

example : arc.outDeg 0 = 1 ∧ arc.inDeg 1 = 1 := by decide
example : arc.inDeg 0 = 0 ∧ arc.outDeg 1 = 0 := by decide
example : cyc3.inDeg 0 + cyc3.outDeg 0 = 2 := by decide
-- edge case: a directed loop adds one to both the in-degree and the out-degree
example : dloop.inDeg 0 = 1 ∧ dloop.outDeg 0 = 1 := by decide

/-! ## `DGraph.IsLoop`, `DGraph.HasMultipleEdges`, `DGraph.IsSimple` -/

example : dloop.IsLoop 0 := by unfold DGraph.IsLoop; decide
example : dup.HasMultipleEdges := by unfold DGraph.HasMultipleEdges; decide
example : arc.IsSimple := by
  unfold DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
-- edge case: (0,1) and (1,0) are different ordered pairs, so this is still simple
example : both.IsSimple := by
  unfold DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
example : ¬ dloop.IsSimple := by
  unfold DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
example : ¬ dup.IsSimple := by
  unfold DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide

/-! ## `IsTournament` -/

example : arc.IsTournament := by
  unfold DGraph.IsTournament DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
example : cyc3.IsTournament := by
  unfold DGraph.IsTournament DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
example : tr3.IsTournament := by
  unfold DGraph.IsTournament DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
-- edge case: both directions present, so "exactly one" fails
example : ¬ both.IsTournament := by
  unfold DGraph.IsTournament DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide
-- edge case: a one-vertex graph is a tournament (no distinct pairs)
example : single.IsTournament := by
  unfold DGraph.IsTournament DGraph.IsSimple DGraph.HasMultipleEdges DGraph.IsLoop; decide

end GraphCh10.Tests
