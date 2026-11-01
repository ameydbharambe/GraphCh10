import GraphCh10.Definitions
import GraphCh10.Lemmas

/-!
# Sanity tests for `GraphCh10.Definitions` (Phases 1, 2, and the Supp. 39 part of Phase 3)

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

/-! # Phase 2 tests (Supp. 10(b), 28) -/

/-! ## `UGraph.HasMultipleEdges`, `UGraph.IsSimple` -/

example : dbl.HasMultipleEdges := by unfold UGraph.HasMultipleEdges; decide
example : ¬ p3.HasMultipleEdges := by unfold UGraph.HasMultipleEdges; decide
example : p3.IsSimple := by
  unfold UGraph.IsSimple UGraph.HasMultipleEdges UGraph.IsLoop; decide
-- edge case: a single loop is not simple
example : ¬ loop1.IsSimple := by
  unfold UGraph.IsSimple UGraph.HasMultipleEdges UGraph.IsLoop; decide
-- edge case: parallel edges are not simple
example : ¬ dbl.IsSimple := by
  unfold UGraph.IsSimple UGraph.HasMultipleEdges UGraph.IsLoop; decide
-- edge case: a graph without edges is simple
example : two0.IsSimple := by
  unfold UGraph.IsSimple UGraph.HasMultipleEdges UGraph.IsLoop; decide

/-! ## `nbrFinset` -/

example : (p3.nbrFinset 1).card = 2 := by decide
example : p3.nbrFinset 1 = {0, 2} := by decide
-- edge case: parallel edges give one neighbour but degree 2
example : (dbl.nbrFinset 0).card = 1 ∧ dbl.deg 0 = 2 := by decide
-- edge case: a loop gives |N(v)| = 1 but degree 2
example : (loop1.nbrFinset 0).card = 1 ∧ loop1.deg 0 = 2 := by decide
-- edge case: an isolated vertex has no neighbours
example : (two0.nbrFinset 0).card = 0 := by decide

/-! ## `SetSimpleGraph`, union, `Isomorphic` -/

/-- K₂ on the vertices {0, 1} inside `Fin 4`. -/
def k2a : SetSimpleGraph (Fin 4) where
  V := {0, 1}
  E := {s(0, 1)}
  edge_sub := by
    rintro p rfl x hx
    -- the endpoints of {0, 1} are 0 and 1
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  loopless := by
    rintro p rfl
    decide

/-- K₂ on the vertices {2, 3} inside `Fin 4`. -/
def k2b : SetSimpleGraph (Fin 4) where
  V := {2, 3}
  E := {s(2, 3)}
  edge_sub := by
    rintro p rfl x hx
    -- the endpoints of {2, 3} are 2 and 3
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  loopless := by
    rintro p rfl
    decide

/-- The graph (∅, ∅) inside `Fin 4`. -/
def emptySSG : SetSimpleGraph (Fin 4) where
  V := ∅
  E := ∅
  edge_sub := by
    rintro p hp
    exact absurd hp (Set.notMem_empty p)
  loopless := by
    rintro p hp
    exact absurd hp (Set.notMem_empty p)

-- union of vertex sets and of edge sets
example : (k2a ∪ k2b).V = {0, 1, 2, 3} := by
  ext x
  change x ∈ ({0, 1} : Set (Fin 4)) ∪ {2, 3} ↔ x ∈ ({0, 1, 2, 3} : Set (Fin 4))
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
example : (k2a ∪ k2b).E = {s(0, 1), s(2, 3)} := by
  ext p
  change p ∈ ({s(0, 1)} : Set (Sym2 (Fin 4))) ∪ {s(2, 3)} ↔
    p ∈ ({s(0, 1), s(2, 3)} : Set (Sym2 (Fin 4)))
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
-- edge case: a graph united with itself is unchanged
example : (k2a ∪ k2a).V = k2a.V ∧ (k2a ∪ k2a).E = k2a.E := by
  constructor
  · exact Set.union_self k2a.V
  · exact Set.union_self k2a.E

/-- Shift by 2: the bijection {0, 1} → {2, 3}. -/
def shift2 : k2a.V ≃ k2b.V where
  toFun x := ⟨x.1 + 2, by
    rcases x with ⟨x, hx⟩
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl⟩
  invFun y := ⟨y.1 - 2, by
    rcases y with ⟨y, hy⟩
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    rcases hx with rfl | rfl <;> rfl
  right_inv y := by
    rcases y with ⟨y, hy⟩
    apply Subtype.ext
    rcases hy with rfl | rfl <;> rfl

-- positive test: K₂ on {0, 1} and K₂ on {2, 3} are isomorphic
example : k2a.Isomorphic k2b := by
  refine ⟨shift2, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  change s(x + 2, y + 2) ∈ ({s(2, 3)} : Set (Sym2 (Fin 4))) ↔
    s(x, y) ∈ ({s(0, 1)} : Set (Sym2 (Fin 4)))
  simp only [Set.mem_singleton_iff]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide
-- edge case: K₂ is not isomorphic to the graph with no vertices
example : ¬ k2a.Isomorphic emptySSG := by
  rintro ⟨f, _⟩
  -- the vertex 0 of K₂ would be sent to a vertex of the empty vertex set
  exact Set.notMem_empty _ (f ⟨0, Or.inl rfl⟩).2

/-! # Phase 3 tests (only the part needed for Supp. 39) -/

/-- The triangle with edges {0,1}, {1,2}, {2,0}. -/
def k3 : UGraph (Fin 3) (Fin 3) :=
  ⟨fun e => if e = 0 then s(0, 1) else if e = 1 then s(1, 2) else s(2, 0)⟩

/-! ## `UGraph.Path` -/

-- positive test: the path 0 – 1 – 2 in `p3`
example : p3.Path 0 2 := .cons 0 rfl (.cons 1 rfl (.nil 2))
-- edge case: the path of length 0
example : p3.Path 0 0 := .nil 0
-- edge case: an edge may be used twice (0 → 1 → 0 over edge 0); undirected edges go both ways
example : p3.Path 0 0 := .cons 0 rfl (.cons 0 (by decide) (.nil 0))
-- edge case: a loop can be traversed repeatedly
example : loop1.Path 0 0 := .cons 0 rfl (.cons 0 rfl (.nil 0))

/-! ## `DGraph.Path` -/

-- positive test: 0 → 1 → 2 in the directed 3-cycle
example : cyc3.Path 0 2 := .cons 0 rfl (.cons 1 rfl (.nil 2))
-- edge case: the path of length 0
example : arc.Path 1 1 := .nil 1
-- edge case: edges cannot be used backwards: no edge of `arc` is associated to (1, 0)
example : ¬ ∃ e, arc.ends e = (1, 0) := by decide

/-- In `arc`, every directed path from 1 stays at 1 (no edge leaves 1). -/
theorem arc_path_from_one {x y : Fin 2} (p : arc.Path x y) (hx : x = 1) : y = 1 := by
  induction p with
  | nil _ => exact hx
  | cons e h _ _ =>
    -- the only edge is (0, 1), which does not start at 1
    subst hx
    have hall : ∀ e' : Fin 1, (arc.ends e').1 ≠ 1 := by decide
    have hfst : (arc.ends e).1 = 1 := by rw [h]
    exact absurd hfst (hall e)

/-! ## `UGraph.Connected` -/

-- positive test: every vertex of `p3` is joined to vertex 1
example : p3.Connected := by
  apply p3.connected_of_forall_path_to 1
  intro x
  match x with
  | 0 => exact ⟨.cons 0 rfl (.nil 1)⟩
  | 1 => exact ⟨.nil 1⟩
  | 2 => exact ⟨.cons 1 (by decide) (.nil 1)⟩
-- edge case: the graph with no vertices is (vacuously) connected
example : empty0.Connected := by
  intro x
  exact x.elim0
/-- In a graph without edges, every path has length 0, so it ends where it starts. -/
theorem two0_path_eq {x y : Fin 2} (p : two0.Path x y) : x = y := by
  induction p with
  | nil _ => rfl
  | cons e _ _ _ => exact e.elim
-- edge case: two isolated vertices are not connected
example : ¬ two0.Connected := by
  intro h
  obtain ⟨p⟩ := h 0 1
  exact absurd (two0_path_eq p) (by decide)

/-! ## `DGraph.StronglyConnected` -/

/-- The directed 3-cycle is strongly connected. -/
theorem cyc3_stronglyConnected : cyc3.StronglyConnected := by
  intro x y
  -- the three edges of the cycle as one-step paths
  have h01 : cyc3.Path 0 1 := .cons 0 rfl (.nil 1)
  have h12 : cyc3.Path 1 2 := .cons 1 rfl (.nil 2)
  have h20 : cyc3.Path 2 0 := .cons 2 rfl (.nil 0)
  match x, y with
  | 0, 0 => exact ⟨.nil 0⟩
  | 0, 1 => exact ⟨h01⟩
  | 0, 2 => exact ⟨.cons 0 rfl h12⟩
  | 1, 0 => exact ⟨.cons 1 rfl h20⟩
  | 1, 1 => exact ⟨.nil 1⟩
  | 1, 2 => exact ⟨h12⟩
  | 2, 0 => exact ⟨h20⟩
  | 2, 1 => exact ⟨.cons 2 rfl h01⟩
  | 2, 2 => exact ⟨.nil 2⟩
-- edge case: a single directed edge is not strongly connected (no path from 1 back to 0)
example : ¬ arc.StronglyConnected := by
  intro h
  obtain ⟨p⟩ := h 1 0
  exact absurd (arc_path_from_one p rfl) (by decide)

/-! ## `deleteEdge` -/

-- `p3 − (edge 0)` keeps the edge {1, 2} and loses the edge {0, 1}
example : (p3.deleteEdge 0).Adj 1 2 := by decide
example : ¬ (p3.deleteEdge 0).Adj 0 1 := by decide
-- edge case: deleting the loop of `loop1` leaves no edges at the vertex
example : (loop1.deleteEdge 0).deg 0 = 0 := by decide

/-! ## `IsCutEdge` -/

/-- In `p3 − (edge 0)`, every path from 0 stays at 0 (no remaining edge touches 0). -/
theorem p3del_path_from_zero {x y : Fin 3} (p : (p3.deleteEdge 0).Path x y) (hx : x = 0) :
    y = 0 := by
  induction p with
  | nil _ => exact hx
  | @cons x x' z e h _ _ =>
    -- no remaining edge is associated to a set {0, x'}
    subst hx
    have hall : ∀ (e' : {e : Fin 2 // e ≠ 0}) (w : Fin 3),
        (p3.deleteEdge 0).ends e' ≠ s(0, w) := by decide
    exact absurd h (hall e x')
-- positive test: the edge {0, 1} of the path 0 – 1 – 2 is a cut edge
example : p3.IsCutEdge 0 := by
  intro h
  obtain ⟨p⟩ := h 0 1
  exact absurd (p3del_path_from_zero p rfl) (by decide)
-- edge case: no edge of a triangle is a cut edge (here edge {0, 1})
example : ¬ k3.IsCutEdge 0 := by
  intro h
  apply h
  -- after deleting {0, 1}, every vertex is still joined to vertex 2
  apply (k3.deleteEdge 0).connected_of_forall_path_to 2
  intro x
  match x with
  | 0 => exact ⟨.cons ⟨2, by decide⟩ (by decide) (.nil 2)⟩
  | 1 => exact ⟨.cons ⟨1, by decide⟩ rfl (.nil 2)⟩
  | 2 => exact ⟨.nil 2⟩

/-! ## `IsOrientation`, `Orientable` -/

-- positive test: directing the triangle as the 3-cycle (0,1), (1,2), (2,0) is an orientation
example : k3.IsOrientation cyc3.ends := by
  refine ⟨?_, cyc3_stronglyConnected⟩
  decide
example : k3.Orientable := by
  refine ⟨cyc3.ends, ?_, cyc3_stronglyConnected⟩
  decide
-- edge case: directing every edge as (0, 1) does not respect the edges of the triangle
example : ¬ k3.IsOrientation (fun _ => (0, 1)) := by
  rintro ⟨h, _⟩
  exact absurd (h 1) (by decide)
-- edge case: two isolated vertices have no orientation (no directed path from 0 to 1)
example : ¬ two0.Orientable := by
  rintro ⟨o, _, hSC⟩
  obtain ⟨p⟩ := hSC 0 1
  -- `two0` has no edges, so every directed path has length 0
  have hEq : ∀ {x y : Fin 2}, (DGraph.mk o).Path x y → x = y := by
    intro x y q
    induction q with
    | nil _ => rfl
    | cons e _ _ _ => exact e.elim
  exact absurd (hEq p) (by decide)

end GraphCh10.Tests
