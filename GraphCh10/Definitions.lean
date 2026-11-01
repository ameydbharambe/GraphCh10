import GraphCh10.Foundations

/-!
# Graph definitions for Rosen Chapter 10

Every notion here is taken from `docs/Chapter_10_Results_Clean_v2.pdf` ("Results"), from a
definition stated in `docs/Chapter_10_Exercises_Clean.pdf` ("Exercises"), or is a clarification
explicitly approved by the project owner (marked **Approved clarification**).

Phase 1 contents: undirected graphs, loops, multigraphs, adjacency, incidence, degree,
neighborhoods; directed graphs, in/out-degree, simple directed graphs, tournaments.

Phase 2 contents (Supp. 10(b), 28): multiple edges, simple graphs, N(v) as a finite set; simple
graphs as literal pairs (V, E), their union, and isomorphism of simple graphs.

Phase 3 contents, only the part needed for Supp. 39: undirected and directed paths, connected and
strongly connected graphs, G − e, cut edges, orientations.

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

/-! ## Phase 2: simple undirected graphs and N(v) as a finite set (Supp. 10(b)) -/

namespace UGraph

variable {V : Type u} {E : Type v} (G : UGraph V E)

/-- **Source:** Results, "multiple edges: distinct edges connecting the same vertices".

Two different edges are associated to the same set of endpoints. -/
def HasMultipleEdges : Prop := ∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ G.ends e₁ = G.ends e₂

/-- **Source:** Results, "simple graph: an undirected graph with no multiple edges or loops". -/
def IsSimple : Prop := ¬ G.HasMultipleEdges ∧ ∀ e : E, ¬ G.IsLoop e

/-- N(v) as a finite set of vertices, so that |N(v)| is its cardinality.

**Lean representation of an approved clarification** (N(v), defined as `nbhd`). This introduces no
new mathematical notion: it is the same set N(v), stored as a `Finset` so that its size |N(v)|
(used in Exercises, Supp. 10) can be counted. It has exactly the same members as `G.nbhd v`; this
is the proved lemma `UGraph.mem_nbrFinset` in `GraphCh10.Lemmas`. It needs finitely many vertices
(`[Fintype V]`) to be a `Finset`, and `[Fintype E] [DecidableEq V]` only to decide adjacency. -/
def nbrFinset [Fintype V] [Fintype E] [DecidableEq V] (v : V) : Finset V :=
  Finset.univ.filter (fun u : V => G.Adj v u)

end UGraph

/-! ## Phase 2: simple graphs as literal pairs (V, E), union, isomorphism (Supp. 28) -/

/-- **Source:** Results, "simple graph: an undirected graph with no multiple edges or loops",
written in the literal form G = (V, E) that Results uses for "subgraph", "G₁ ∪ G₂" and "isomorphic
simple graphs" ("{v₁, v₂} ∈ E₁").

**Approved design** (second layer, used for Supp. 28). The vertices and edges live inside an ambient
type `α`, so that unions V₁ ∪ V₂ and E₁ ∪ E₂ make sense:
* `V` is the vertex set and `E` is the edge set, each edge being a set {u, w} (`Sym2 α`);
* `edge_sub`: the endpoints of every edge are vertices of the graph;
* `loopless`: no edge is a loop.
Because `E` is a *set* of endpoint pairs, the same pair cannot occur twice: there are no multiple
edges.

**Classification.**
* *Direct translation:* identifying each edge with its set of endpoints is exactly the notation
  "{v₁, v₂} ∈ E" that Results uses for simple graphs. Nothing is lost for simple graphs: with no
  multiple edges, edges correspond one-to-one to their endpoint sets.
* *Modeling convention:* the ambient type `α` is needed only so that V₁ ∪ V₂ and E₁ ∪ E₂ make
  sense; Results presupposes such a common universe when it forms unions.
* *Relation to `UGraph.IsSimple`:* a `SetSimpleGraph` and a `UGraph` satisfying `IsSimple`
  describe the same mathematical objects (simple graphs) in two representations. This
  correspondence is argued on paper here; it is **not** a proved Lean theorem in this project. -/
structure SetSimpleGraph (α : Type u) where
  /-- The vertex set V. -/
  V : Set α
  /-- The edge set E; each edge is the set {u, w} of its endpoints. -/
  E : Set (Sym2 α)
  /-- Every endpoint of an edge is a vertex. -/
  edge_sub : ∀ p ∈ E, ∀ x ∈ p, x ∈ V
  /-- No edge is a loop. -/
  loopless : ∀ p ∈ E, ¬ p.IsDiag

namespace SetSimpleGraph

variable {α : Type u} {β : Type v}

/-- **Source:** Results, "G₁ ∪ G₂ (union of G₁ and G₂): the graph (V₁ ∪ V₂, E₁ ∪ E₂), where
G₁ = (V₁, E₁) and G₂ = (V₂, E₂)".

The union of two simple graphs is again simple: its edges still have their endpoints among the
vertices, and it still has no loops.

**Scope note.** Results defines the union for arbitrary graphs; here it is defined only between
two `SetSimpleGraph`s in the same ambient type. This suffices for Supp. 28, whose subject is
isomorphism, which Results defines only for simple graphs. -/
protected def union (G₁ G₂ : SetSimpleGraph α) : SetSimpleGraph α where
  V := G₁.V ∪ G₂.V
  E := G₁.E ∪ G₂.E
  edge_sub := by
    rintro p (hp | hp) x hx
    · exact Or.inl (G₁.edge_sub p hp x hx)
    · exact Or.inr (G₂.edge_sub p hp x hx)
  loopless := by
    rintro p (hp | hp)
    · exact G₁.loopless p hp
    · exact G₂.loopless p hp

/-- The notation `G₁ ∪ G₂` for `SetSimpleGraph.union`. -/
instance : Union (SetSimpleGraph α) := ⟨SetSimpleGraph.union⟩

/-- **Source:** Results, "isomorphic simple graphs: the simple graphs G₁ = (V₁, E₁) and
G₂ = (V₂, E₂) are isomorphic if there exists a one-to-one correspondence f from V₁ to V₂ such that
{f(v₁), f(v₂)} ∈ E₂ if and only if {v₁, v₂} ∈ E₁ for all v₁ and v₂ in V₁".

A one-to-one correspondence from V₁ to V₂ is a bijection `G₁.V ≃ G₂.V`. The two graphs may live in
different ambient types. -/
def Isomorphic (G₁ : SetSimpleGraph α) (G₂ : SetSimpleGraph β) : Prop :=
  ∃ f : G₁.V ≃ G₂.V, ∀ v₁ v₂ : G₁.V,
    s((f v₁ : β), (f v₂ : β)) ∈ G₂.E ↔ s((v₁ : α), (v₂ : α)) ∈ G₁.E

end SetSimpleGraph

/-! ## Phase 3 (part needed for Supp. 39): paths, connectivity, cut edges, orientations -/

namespace UGraph

variable {V : Type u} {E : Type v}

/-- **Source:** Results, "path from u to v in an undirected graph: a sequence of edges
e₁, e₂, …, eₙ, where eᵢ is associated to {xᵢ, xᵢ₊₁} for i = 0, 1, …, n, where x₀ = u and
xₙ₊₁ = v".

**Approved reading (A1)** of the indexing in that text: vertices x₀, …, xₙ with eᵢ associated to
{xᵢ₋₁, xᵢ}, x₀ = u and xₙ = v. A path of length 0 (`nil`) is allowed. Paths may repeat edges and
vertices; only a "simple path" forbids repeated edges.

`cons e h p` is the path that starts with edge `e` from `x` to `y` (`h` says `e` is associated to
{x, y}) and continues with the path `p` from `y` to `z`.

**Representation (equivalent).** Results describes a path as the edge sequence e₁, …, eₙ, with the
vertices x₀, …, xₙ only required to exist. A `Path` stores the edges together with those vertices
(each `cons` records the next vertex). Since this project only ever uses the *existence* of a path
(`Nonempty (G.Path u v)`), the two descriptions are equivalent. Length 0 is justified by Results,
"circuit: a path of length n ≥ 1", which presupposes that shorter paths exist. -/
inductive Path (G : UGraph V E) : V → V → Type (max u v)
  /-- The path of length 0 at `x`. -/
  | nil (x : V) : Path G x x
  /-- First the edge `e` associated to {x, y}, then a path from `y` to `z`. -/
  | cons {x y z : V} (e : E) (h : G.ends e = s(x, y)) (p : Path G y z) : Path G x z

/-- **Source:** Results, "connected graph: an undirected graph with the property that there is a
path between every pair of vertices".

**Approved reading (A2):** graphs with 0 or 1 vertices are (vacuously) connected.

**Pairs with x = y.** The definition quantifies over all `x y`, including `x = y`. That case is
always satisfied by the path of length 0 (`Path.nil`), so this is equivalent to requiring a path
between every pair of *distinct* vertices. -/
def Connected (G : UGraph V E) : Prop := ∀ x y : V, Nonempty (G.Path x y)

/-- G − e₀: the graph obtained from G by removing the edge `e₀` only.

**Approved clarification (M3)** of "G − e", which Results uses in "cut edge" without defining it.
The vertices are unchanged; the edges are those of G other than `e₀`, with the same endpoints. -/
def deleteEdge (G : UGraph V E) (e₀ : E) : UGraph V {e : E // e ≠ e₀} :=
  ⟨fun e => G.ends e.1⟩

/-- **Source:** Results, "cut edge of G: an edge e such that G − e is disconnected".

"Disconnected" is read as "not connected".

**Literal reading; differs from the standard definition on disconnected graphs.** This follows the
supplied Results text exactly. It differs from the standard graph-theoretic definition (an edge
whose deletion increases the number of connected components, a "bridge") on graphs that are
*already disconnected*: there, G − e is disconnected for every edge e, so **every** edge satisfies
`IsCutEdge`, even when deleting it does not increase the number of connected components. On
connected graphs the two readings agree. The literal definition is retained deliberately, because
this project prioritizes fidelity to the approved source; the bridge definition is not used.
(For Supp. 39 this only enlarges the set of graphs satisfying the hypothesis "G has a cut edge";
those extra graphs are disconnected and hence not orientable, so the exercise is unaffected.) -/
def IsCutEdge (G : UGraph V E) (e : E) : Prop := ¬ (G.deleteEdge e).Connected

end UGraph

namespace DGraph

variable {V : Type u} {E : Type v}

/-- **Source:** Results, "path from u to v in a graph with directed edges: a sequence of edges
e₁, e₂, …, eₙ, where eᵢ is associated to (xᵢ, xᵢ₊₁) for i = 0, 1, …, n, where x₀ = u and
xₙ₊₁ = v".

**Approved reading (A1)**, as for undirected paths: eᵢ is associated to the ordered pair
(xᵢ₋₁, xᵢ), x₀ = u, xₙ = v; length 0 is allowed; edges and vertices may repeat. Every edge is
traversed from its initial vertex to its terminal vertex.

**Representation (equivalent)**, as for `UGraph.Path`: the edges are stored together with the
vertices x₀, …, xₙ whose existence Results requires; only the existence of a path is ever used. -/
inductive Path (G : DGraph V E) : V → V → Type (max u v)
  /-- The path of length 0 at `x`. -/
  | nil (x : V) : Path G x x
  /-- First the edge `e` associated to (x, y), then a path from `y` to `z`. -/
  | cons {x y z : V} (e : E) (h : G.ends e = (x, y)) (p : Path G y z) : Path G x z

/-- **Source:** Results, "strongly connected directed graph: a directed graph with the property
that there is a directed path from every vertex to every vertex". -/
def StronglyConnected (G : DGraph V E) : Prop := ∀ x y : V, Nonempty (G.Path x y)

end DGraph

namespace UGraph

variable {V : Type u} {E : Type v}

/-- **Source:** Exercises, before Supp. 35, "An orientation of an undirected simple graph is an
assignment of directions to its edges such that the resulting directed graph is strongly
connected."

An assignment of directions is a map `o` sending each edge `e` to an ordered pair whose set of
entries is the set {u, w} associated to `e` in G (so `e` becomes (u, w) or (w, u)). The resulting
directed graph has the same edges, with `o` as its ordered pairs.

**Classification: direct translation.** The first conjunct says exactly that each edge {u, w} is
given one of its two directions; the resulting directed graph `DGraph.mk o` has the same vertices
(`V`) and the same edges (`E`) as G. The second conjunct is the "such that the resulting directed
graph is strongly connected" clause, bundled into the definition as in the source sentence.

**Approved reading (A7):** the source defines orientations only for simple graphs. This definition
does not build simplicity in; exercises that use it assume `G.IsSimple` explicitly. -/
def IsOrientation (G : UGraph V E) (o : E → V × V) : Prop :=
  (∀ e : E, s((o e).1, (o e).2) = G.ends e) ∧ (DGraph.mk o).StronglyConnected

/-- **Source:** Exercises, before Supp. 35, "When an orientation of an undirected graph exists,
this graph is called orientable."

**Approved reading (A7):** as for `IsOrientation`, the source defines orientations only for simple
graphs. `Orientable` is stated for every `UGraph`; exercises that use it (Supp. 39) assume
`G.IsSimple` as a separate hypothesis. -/
def Orientable (G : UGraph V E) : Prop := ∃ o : E → V × V, G.IsOrientation o

end UGraph

end GraphCh10
