-- STATUS: UNFINISHED

import GraphCh10.Definitions
import GraphCh10.Lemmas

/-!
# Supplementary Exercise 39

Paper proof. Let G be a simple graph with a cut edge e₀, and suppose, for contradiction, that G has
an orientation o. In the resulting directed graph, e₀ is directed from some vertex a (its tail) to
some vertex b.

**Key step.** Every directed path from a vertex x to the tail a can be turned into an undirected
path from x to a that avoids e₀. By induction on the directed path:
* if the path is empty, then x = a and the empty path works;
* if the path starts with an edge e from x to y and continues to a:
  - if e = e₀, then x is the tail of e₀, so x = a and the empty path works;
  - if e ≠ e₀, then e is still an edge of G − e₀, associated to {x, y}; put it in front of the
    undirected path from y to a (avoiding e₀) given by the induction hypothesis.

**Conclusion.** Because the orientation is strongly connected, every vertex x has a directed path to
a, hence an undirected path to a in G − e₀. All vertices are joined to a in G − e₀, so G − e₀ is
connected. This contradicts e₀ being a cut edge. Hence G has no orientation: it is not orientable.
-/

namespace GraphCh10

universe u v

namespace Supp39

variable {V : Type u} {E : Type v}

/-- **A directed path ending at the tail of e₀ gives an undirected path avoiding e₀.**

Let `o` direct every edge of G (each edge `e` becomes the ordered pair `o e`, whose set of entries
is the set G associates to `e`), and let `a` be the tail (initial vertex) of the edge `e₀` under
`o`. Then every directed path from `x` to `a` in the resulting directed graph yields an undirected
path from `x` to `a` in G − e₀. -/
theorem path_avoiding_of_dpath_to_tail (G : UGraph V E) (o : E → V × V)
    (hdir : ∀ e : E, s((o e).1, (o e).2) = G.ends e) (e₀ : E) {a : V} (ha : (o e₀).1 = a)
    {x : V} (p : (DGraph.mk o).Path x a) : Nonempty ((G.deleteEdge e₀).Path x a) := by
  induction p with
  | nil x =>
    -- the empty directed path at `a` becomes the empty undirected path at `a`
    exact ⟨UGraph.Path.nil x⟩
  | @cons x y z e h p ih =>
    -- `h` says the first edge `e` is directed from `x` to `y`
    have hxy : o e = (x, y) := h
    by_cases he : e = e₀
    · -- the first edge is e₀ itself: then `x` is the tail of e₀, i.e. `x = a`
      have hxa : x = z := by
        calc x = (o e).1 := by rw [hxy]
          _ = (o e₀).1 := by rw [he]
          _ = z := ha
      -- so the empty path at `x` already goes from `x` to `a`
      subst hxa
      exact ⟨UGraph.Path.nil x⟩
    · -- the first edge is not e₀, so it is still an edge of G − e₀, associated to {x, y}
      have hends : (G.deleteEdge e₀).ends ⟨e, he⟩ = s(x, y) := by
        calc (G.deleteEdge e₀).ends ⟨e, he⟩ = G.ends e := rfl
          _ = s((o e).1, (o e).2) := (hdir e).symm
          _ = s(x, y) := by rw [hxy]
      -- the rest of the path, from `y` to `a`, becomes an undirected path avoiding e₀
      obtain ⟨q⟩ := ih ha
      -- put the edge `e` in front of it
      exact ⟨UGraph.Path.cons ⟨e, he⟩ hends q⟩

end Supp39

open Supp39

/-- **Supplementary Exercise 39.** "Show that a graph is not orientable if it has a cut edge."

**Approved hypothesis.** `G.IsSimple`: the Exercises define an orientation only for "an undirected
simple graph", so "orientable" presupposes that G is simple. (The proof below does not need this
hypothesis, so its binder is named `_hG`; it is kept because it is part of the approved
statement.) -/
theorem supp39 {V : Type u} {E : Type v} (G : UGraph V E) (_hG : G.IsSimple)
    (hcut : ∃ e : E, G.IsCutEdge e) : ¬ G.Orientable := by
  -- take a cut edge e₀ and, for contradiction, an orientation `o` of G
  obtain ⟨e₀, he₀⟩ := hcut
  rintro ⟨o, hdir, hstrong⟩
  -- let `a` be the tail of e₀ in the resulting directed graph
  set a : V := (o e₀).1
  -- every vertex `x` has a directed path to `a`, so an undirected path to `a` avoiding e₀
  have hreach : ∀ x : V, Nonempty ((G.deleteEdge e₀).Path x a) := by
    intro x
    obtain ⟨p⟩ := hstrong x a
    exact path_avoiding_of_dpath_to_tail G o hdir e₀ rfl p
  -- hence G − e₀ is connected
  have hconn : (G.deleteEdge e₀).Connected :=
    (G.deleteEdge e₀).connected_of_forall_path_to a hreach
  -- but e₀ is a cut edge, so G − e₀ is not connected
  exact he₀ hconn

end GraphCh10
