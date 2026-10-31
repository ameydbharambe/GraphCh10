import GraphCh10.Foundations

/-!
# Graph definitions for Rosen Chapter 10

Every notion here is taken from `docs/Chapter_10_Results_Clean_v2.pdf` ("Results"), from a
definition stated in `docs/Chapter_10_Exercises_Clean.pdf` ("Exercises"), or is a clarification
explicitly approved by the project owner (marked **Approved clarification**).

Phase 1 contents: undirected graphs, loops, multigraphs, adjacency, incidence, degree,
neighborhoods; directed graphs, in/out-degree, simple directed graphs, tournaments.

Conventions:
* Vertices of a graph are the elements of a type `V`, edges the elements of a type `E`.
  Finiteness is never built in; exercises that need it assume `[Fintype V]` / `[Fintype E]`.
* `[DecidableEq V]` only lets us compute with `Finset.filter`; it is not a mathematical assumption.
-/

namespace GraphCh10

universe u v

/-! ## Undirected graphs -/

/-- **Source:** Results, "undirected graph: a set of vertices and a set of undirected edges each of
which is associated with a set of one or two of these vertices", and "undirected edge: an edge
associated to a set {u, v}, where u and v are vertices".

The vertices are the elements of `V`, the edges are the elements of `E`, and `ends e` is the set
associated to the edge `e`. An element `s(u, w) : Sym2 V` is exactly a set {u, w} with one element
(`u = w`) or two elements. Distinct edges may have the same `ends`, which models multiple edges. -/
structure UGraph (V : Type u) (E : Type v) where
  /-- The set {u, v} of endpoints associated to each edge. -/
  ends : E → Sym2 V

namespace UGraph

variable {V : Type u} {E : Type v} (G : UGraph V E)

/-- **Source:** Results, "loop: an edge connecting a vertex with itself".

The edge `e` is a loop when its associated set has a single element. -/
def IsLoop (e : E) : Prop := (G.ends e).IsDiag

/-- **Source:** Results, "multigraph: an undirected graph that may contain multiple edges but no
loops".

Multiple edges are allowed but not required; only loops are forbidden. (A pseudograph, "an
undirected graph that may contain multiple edges and loops", is an arbitrary `UGraph`.) -/
def IsMultigraph : Prop := ∀ e : E, ¬ G.IsLoop e

/-- **Source:** Results, "adjacent: two vertices are adjacent if there is an edge between them".

`u` and `w` are adjacent when some edge is associated to the set {u, w}. This is symmetric because
`s(u, w) = s(w, u)`, and a loop at `v` makes `v` adjacent to itself. -/
def Adj (u w : V) : Prop := ∃ e : E, G.ends e = s(u, w)

instance [Fintype E] [DecidableEq V] : DecidableRel G.Adj :=
  fun u w => inferInstanceAs (Decidable (∃ e : E, G.ends e = s(u, w)))

/-- **Source:** Results, "incident: an edge is incident with a vertex if the vertex is an endpoint
of that edge". -/
def Incident (e : E) (v : V) : Prop := v ∈ G.ends e

instance [DecidableEq V] (e : E) (v : V) : Decidable (G.Incident e v) :=
  inferInstanceAs (Decidable (v ∈ G.ends e))

/-- **Source:** Results, "deg v (degree of the vertex v in an undirected graph): the number of
edges incident with v with loops counted twice".

The first summand counts every edge incident with `v` once; the second counts the loops at `v`
(edges associated to {v}) a second time. -/
def deg [Fintype E] [DecidableEq V] (v : V) : ℕ :=
  (Finset.univ.filter (fun e : E => G.Incident e v)).card +
    (Finset.univ.filter (fun e : E => G.ends e = s(v, v))).card

/-- N(v), the neighborhood of `v`: the set of vertices adjacent to `v`.

**Approved clarification.** N(v) is used in Exercises, Supp. 10, but is not defined in either PDF.
Following "adjacent" in Results, a loop at `v` puts `v` in N(v). -/
def nbhd (v : V) : Set V := {u | G.Adj v u}

/-- N(A), the neighborhood of a set A of vertices: the set of all vertices
adjacent to at least one vertex in A.

**Source:** Rosen, Discrete Mathematics and Its Applications, 8th Edition,
Section 10.2, Definition 2.

**Approved clarification.** This definition was independently verified against
Rosen's textbook and approved by the project owner. Although N(A) appears in
the provided Exercises and Results PDFs, its explicit definition was omitted.
No additional mathematical assumptions are introduced. -/
def nbhdSet (A : Set V) : Set V := {u | ∃ a ∈ A, G.Adj a u}

end UGraph

/-! ## Directed graphs -/

/-- **Source:** Results, "directed graph: a set of vertices together with a set of directed edges
each of which is associated with an ordered pair of vertices", and "directed edge: an edge
associated to an ordered pair (u, v), where u and v are vertices".

`ends e = (u, w)` means `e` is associated to the ordered pair (u, w): `u` is its initial vertex and
`w` its terminal vertex. Distinct edges may share the same pair (multiple directed edges). -/
structure DGraph (V : Type u) (E : Type v) where
  /-- The ordered pair (initial vertex, terminal vertex) associated to each edge. -/
  ends : E → V × V

namespace DGraph

variable {V : Type u} {E : Type v} (G : DGraph V E)

/-- "(u, w) is an edge of the graph": some edge is associated to the ordered pair (u, w).

**Source:** Exercises, tournament definition before Supp. 40, "exactly one of (u, v) and (v, u) is
an edge of the graph". -/
def DAdj (u w : V) : Prop := ∃ e : E, G.ends e = (u, w)

instance [Fintype E] [DecidableEq V] : DecidableRel G.DAdj :=
  fun u w => inferInstanceAs (Decidable (∃ e : E, G.ends e = (u, w)))

/-- **Source:** Results, "deg⁻(v) (the in-degree of the vertex v in a graph with directed edges):
the number of edges with v as their terminal vertex". -/
def inDeg [Fintype E] [DecidableEq V] (v : V) : ℕ :=
  (Finset.univ.filter (fun e : E => (G.ends e).2 = v)).card

/-- **Source:** Results, "deg⁺(v) (the out-degree of the vertex v in a graph with directed edges):
the number of edges with v as their initial vertex". -/
def outDeg [Fintype E] [DecidableEq V] (v : V) : ℕ :=
  (Finset.univ.filter (fun e : E => (G.ends e).1 = v)).card

/-- A directed loop: an edge whose initial and terminal vertices coincide.

**Source:** Results, "loop: an edge connecting a vertex with itself". -/
def IsLoop (e : E) : Prop := (G.ends e).1 = (G.ends e).2

/-- **Source:** Results, "multiple directed edges: distinct directed edges associated with the same
ordered pair (u,v), where u and v are vertices". -/
def HasMultipleEdges : Prop := ∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ G.ends e₁ = G.ends e₂

/-- **Source:** Results, "simple directed graph: a directed graph without loops or multiple
directed edges". -/
def IsSimple : Prop := ¬ G.HasMultipleEdges ∧ ∀ e : E, ¬ G.IsLoop e

/-- **Source:** Exercises, before Supp. 40, "A tournament is a simple directed graph such that if u
and v are distinct vertices in the graph, exactly one of (u, v) and (v, u) is an edge of the
graph." -/
def IsTournament : Prop :=
  G.IsSimple ∧ ∀ u w : V, u ≠ w → Xor (G.DAdj u w) (G.DAdj w u)

end DGraph

end GraphCh10
