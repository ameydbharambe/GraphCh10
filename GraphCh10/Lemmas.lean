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

end GraphCh10
