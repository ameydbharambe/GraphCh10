-- STATUS: COMPLETE

import GraphCh10.Definitions
import GraphCh10.Lemmas

/-!
# Supplementary Exercise 41

**Answer: n − 1**, where n is the number of vertices of the tournament.

Paper proof. Fix a vertex v of a tournament G with n vertices.
1. G has no multiple directed edges, so the edges leaving v correspond one-to-one to their
   terminal vertices: deg⁺(v) = #{w | (v, w) is an edge}. Likewise
   deg⁻(v) = #{w | (w, v) is an edge}.
2. G has no loops, so neither set contains v itself.
3. For each of the n − 1 vertices w ≠ v, exactly one of (v, w) and (w, v) is an edge, so the
   in-neighbours of v are exactly the vertices w ≠ v that are not out-neighbours of v.
   Hence the two sets split the n − 1 vertices other than v, and deg⁻(v) + deg⁺(v) = n − 1.
-/

namespace GraphCh10

universe u v

namespace Supp41

variable {V : Type u} {E : Type v} (G : DGraph V E)

/-- In a simple directed graph, the out-degree of `v` is the number of vertices `w` such that
(v, w) is an edge: the edges with initial vertex `v` correspond one-to-one to their terminal
vertices. -/
theorem outDeg_eq_card_outNbrs [Fintype V] [Fintype E] [DecidableEq V]
    (hS : G.IsSimple) (v : V) :
    G.outDeg v = (Finset.univ.filter (fun w : V => G.DAdj v w)).card := by
  -- the edges with initial vertex `v`
  let leaving : Finset E := Finset.univ.filter (fun e : E => (G.ends e).1 = v)
  -- the terminal vertices of the edges leaving `v` are exactly the out-neighbours of `v`
  have himage : leaving.image (fun e : E => (G.ends e).2) =
      Finset.univ.filter (fun w : V => G.DAdj v w) := by
    ext w
    simp only [leaving, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold DGraph.DAdj
    constructor
    · -- an edge e with ends e = (v, w') and w' = w is associated to the pair (v, w)
      rintro ⟨e, he1, he2⟩
      exact ⟨e, Prod.ext he1 he2⟩
    · -- an edge associated to (v, w) leaves `v` and has terminal vertex `w`
      rintro ⟨e, he⟩
      exact ⟨e, by rw [he], by rw [he]⟩
  -- two edges leaving `v` with the same terminal vertex have the same ordered pair, so are equal
  have hinj : Set.InjOn (fun e : E => (G.ends e).2) leaving := by
    intro e₁ h₁ e₂ h₂ hsnd
    simp only [leaving, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      at h₁ h₂
    apply G.ends_injective_of_isSimple hS
    exact Prod.ext (h₁.trans h₂.symm) hsnd
  -- counting the edges leaving `v` is counting their (distinct) terminal vertices
  calc G.outDeg v = leaving.card := rfl
    _ = (leaving.image (fun e : E => (G.ends e).2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ = (Finset.univ.filter (fun w : V => G.DAdj v w)).card := by rw [himage]

/-- In a simple directed graph, the in-degree of `v` is the number of vertices `w` such that
(w, v) is an edge: the edges with terminal vertex `v` correspond one-to-one to their initial
vertices. -/
theorem inDeg_eq_card_inNbrs [Fintype V] [Fintype E] [DecidableEq V]
    (hS : G.IsSimple) (v : V) :
    G.inDeg v = (Finset.univ.filter (fun w : V => G.DAdj w v)).card := by
  -- the edges with terminal vertex `v`
  let entering : Finset E := Finset.univ.filter (fun e : E => (G.ends e).2 = v)
  -- the initial vertices of the edges entering `v` are exactly the in-neighbours of `v`
  have himage : entering.image (fun e : E => (G.ends e).1) =
      Finset.univ.filter (fun w : V => G.DAdj w v) := by
    ext w
    simp only [entering, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold DGraph.DAdj
    constructor
    · -- an edge e with ends e = (w', v) and w' = w is associated to the pair (w, v)
      rintro ⟨e, he2, he1⟩
      exact ⟨e, Prod.ext he1 he2⟩
    · -- an edge associated to (w, v) enters `v` and has initial vertex `w`
      rintro ⟨e, he⟩
      exact ⟨e, by rw [he], by rw [he]⟩
  -- two edges entering `v` with the same initial vertex have the same ordered pair, so are equal
  have hinj : Set.InjOn (fun e : E => (G.ends e).1) entering := by
    intro e₁ h₁ e₂ h₂ hfst
    simp only [entering, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      at h₁ h₂
    apply G.ends_injective_of_isSimple hS
    exact Prod.ext hfst (h₁.trans h₂.symm)
  -- counting the edges entering `v` is counting their (distinct) initial vertices
  calc G.inDeg v = entering.card := rfl
    _ = (entering.image (fun e : E => (G.ends e).1)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ = (Finset.univ.filter (fun w : V => G.DAdj w v)).card := by rw [himage]

/-- In a directed graph without loops, no vertex `v` has (v, v) as an edge. -/
theorem not_dAdj_self (hS : G.IsSimple) (v : V) : ¬ G.DAdj v v := by
  -- an edge associated to (v, v) would be a loop
  rintro ⟨e, he⟩
  exact hS.2 e (by rw [DGraph.IsLoop, he])

end Supp41

open Supp41

/-- **Supplementary Exercise 41.** "What is the sum of the in-degree and out-degree of a vertex
in a tournament?"

Answer: n − 1, where n = |V| is the number of vertices. Tournament (Exercises, before Supp. 40):
"a simple directed graph such that if u and v are distinct vertices in the graph, exactly one of
(u, v) and (v, u) is an edge of the graph." `[Fintype V] [Fintype E]` make the degrees and the
vertex count finite numbers; `[DecidableEq V]` is only needed to compute with `Finset.filter`. -/
theorem supp41 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : DGraph V E) (hG : G.IsTournament) (v : V) :
    G.inDeg v + G.outDeg v = Fintype.card V - 1 := by
  -- a tournament is simple, and distinct vertices have exactly one edge between them
  obtain ⟨hSimple, hExactlyOne⟩ := hG
  -- the vertices other than `v`
  let others : Finset V := Finset.univ.erase v
  -- (step 1) deg⁺(v) counts the out-neighbours of `v`, which are all different from `v` (step 2)
  have hOut : G.outDeg v = (others.filter (fun w : V => G.DAdj v w)).card := by
    rw [outDeg_eq_card_outNbrs G hSimple v]
    congr 1
    ext w
    simp only [others, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    constructor
    · -- an out-neighbour of `v` is not `v`, since there are no loops
      intro hvw
      refine ⟨?_, hvw⟩
      rintro rfl
      exact not_dAdj_self G hSimple w hvw
    · -- conversely, keep only the edge fact
      exact fun h => h.2
  -- (steps 1 and 3) deg⁻(v) counts the vertices w ≠ v that are not out-neighbours of `v`
  have hIn : G.inDeg v = (others.filter (fun w : V => ¬ G.DAdj v w)).card := by
    rw [inDeg_eq_card_inNbrs G hSimple v]
    congr 1
    ext w
    simp only [others, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    constructor
    · -- if (w, v) is an edge, then w ≠ v (no loops) and (v, w) is not an edge (exactly one)
      intro hwv
      have hne : w ≠ v := by
        rintro rfl
        exact not_dAdj_self G hSimple w hwv
      refine ⟨hne, ?_⟩
      rcases hExactlyOne w v hne with ⟨_, hnvw⟩ | ⟨hvw, hnwv⟩
      · exact hnvw
      · exact absurd hwv hnwv
    · -- if w ≠ v and (v, w) is not an edge, then (w, v) is an edge (exactly one)
      rintro ⟨hne, hnvw⟩
      rcases hExactlyOne w v hne with ⟨hwv, _⟩ | ⟨hvw, _⟩
      · exact hwv
      · exact absurd hvw hnvw
  -- the in- and out-neighbours of `v` split the n − 1 vertices other than `v`
  calc G.inDeg v + G.outDeg v
      = (others.filter (fun w : V => G.DAdj v w)).card +
          (others.filter (fun w : V => ¬ G.DAdj v w)).card := by
        rw [hIn, hOut, Nat.add_comm]
    _ = others.card := Finset.card_filter_add_card_filter_not _
    _ = Fintype.card V - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

end GraphCh10
