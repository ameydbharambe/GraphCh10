import GraphCh10.Definitions

/-!
# Shared lemmas for Rosen Chapter 10

Reusable facts about the notions in `GraphCh10.Definitions`, each proved (no axioms).
-/

namespace GraphCh10

universe u v

namespace DGraph

variable {V : Type u} {E : Type v} (G : DGraph V E)

/-- In a directed graph without multiple directed edges, different edges have different ordered
pairs: the map `ends : E → V × V` is injective. -/
theorem ends_injective_of_isSimple (hG : G.IsSimple) : Function.Injective G.ends := by
  intro e₁ e₂ hends
  -- if `e₁ ≠ e₂`, the two edges would be multiple directed edges
  by_contra hne
  exact hG.1 ⟨e₁, e₂, hne, hends⟩

/-- A simple directed graph on finitely many vertices has finitely many edges: its edges inject
into the finite set of ordered pairs of vertices. This shows the `[Fintype E]` hypothesis used with
in/out-degrees adds no restriction for simple directed graphs (e.g. tournaments). -/
theorem finite_edges_of_isSimple [Finite V] (hG : G.IsSimple) : Finite E := by
  -- choose a `Fintype` structure on the finite vertex type
  have : Fintype V := Fintype.ofFinite V
  -- the finite set of all ordered pairs of vertices
  let pairs : Finset (V × V) := Finset.univ ×ˢ Finset.univ
  -- send each edge to its ordered pair, viewed as an element of `pairs`
  let f : E → pairs := fun e => ⟨G.ends e, by simp [pairs]⟩
  -- this map is injective because `ends` is
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    exact G.ends_injective_of_isSimple hG (congrArg Subtype.val h)
  exact Finite.of_injective f hf

end DGraph

namespace UGraph

variable {V : Type u} {E : Type v} (G : UGraph V E)

/-- The finite set `G.nbrFinset v` has exactly the members of N(v) = `G.nbhd v`. -/
theorem mem_nbrFinset [Fintype V] [Fintype E] [DecidableEq V] (v u : V) :
    u ∈ G.nbrFinset v ↔ u ∈ G.nbhd v := by
  -- both sides say that `u` is adjacent to `v`
  simp only [nbrFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Paths can be joined: a path from `x` to `y` followed by a path from `y` to `z` gives a path from
`x` to `z`. -/
theorem path_trans {x y z : V} (p : G.Path x y) (hq : Nonempty (G.Path y z)) :
    Nonempty (G.Path x z) := by
  obtain ⟨q⟩ := hq
  induction p with
  | nil _ =>
    -- the empty path at `x` adds nothing
    exact ⟨q⟩
  | cons e h _ ih =>
    -- keep the first edge `e` and join the rest of the path with `q`
    obtain ⟨r⟩ := ih q
    exact ⟨Path.cons e h r⟩

/-- Undirected paths can be reversed: a path from `x` to `y` gives a path from `y` to `x`. -/
theorem path_symm {x y : V} (p : G.Path x y) : Nonempty (G.Path y x) := by
  induction p with
  | nil x =>
    -- the empty path is its own reverse
    exact ⟨Path.nil x⟩
  | @cons x x' z e h _ ih =>
    -- the edge `e` is associated to {x, x'} = {x', x}, so it is a one-edge path from `x'` to `x`
    have hback : G.ends e = s(x', x) := by rw [h, Sym2.eq_swap]
    have hstep : Nonempty (G.Path x' x) := ⟨Path.cons e hback (Path.nil x)⟩
    -- reverse the rest (from `z` to `x'`), then take the edge back to `x`
    obtain ⟨r⟩ := ih
    exact G.path_trans r hstep

/-- If every vertex is joined by a path to one fixed vertex `c`, the graph is connected. -/
theorem connected_of_forall_path_to (c : V) (h : ∀ x : V, Nonempty (G.Path x c)) :
    G.Connected := by
  intro x y
  -- a path from `x` to `c`
  obtain ⟨p⟩ := h x
  -- a path from `c` to `y`: reverse a path from `y` to `c`
  obtain ⟨q⟩ := h y
  have hcy : Nonempty (G.Path c y) := G.path_symm q
  -- join them at `c`
  exact G.path_trans p hcy

end UGraph

end GraphCh10
