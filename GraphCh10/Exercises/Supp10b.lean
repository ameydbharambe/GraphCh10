-- STATUS: COMPLETE

import GraphCh10.Definitions
import GraphCh10.Lemmas

/-!
# Supplementary Exercise 10(b)

Paper proof. Fix a vertex v. Write I(v) for the set of edges incident with v and L(v) for the set
of loops at v, so that deg v = |I(v)| + |L(v)| (each loop is counted a second time).
Send each edge e ∈ I(v) to its *other endpoint*: the vertex u with e associated to {v, u}
(u = v when e is a loop). This map sends I(v) onto N(v):
* its values are neighbours of v, because e itself joins v and u;
* every neighbour u of v is reached, by any edge joining v and u.
Hence |N(v)| = |image| ≤ |I(v)| ≤ |I(v)| + |L(v)| = deg v, and
**|N(v)| = deg v exactly when L(v) = ∅ and the map is one-to-one on I(v).**

(⇐) Let G be simple. With no loops, L(v) = ∅. If two edges incident with v have the same other
endpoint u, both are associated to {v, u}; with no multiple edges they are the same edge. So the map
is one-to-one and |N(v)| = deg v.

(⇒) Suppose |N(v)| = deg v for every v.
* *No loops:* a loop at a puts itself in L(a), so L(a) ≠ ∅ and |N(a)| < deg a.
  Intuitively, a loop adds 2 to deg a but adds at most the single neighbour a to N(a).
* *No multiple edges:* two different edges e₁, e₂ both associated to {a, b} are incident with a and
  have the same other endpoint b, so the map is not one-to-one and |N(a)| < deg a.
  Intuitively, the second parallel edge adds 1 to deg a but no new neighbour.
Both contradict |N(a)| = deg a, so G is simple.
-/

namespace GraphCh10

universe u v

namespace Supp10b

variable {V : Type u} {E : Type v} (G : UGraph V E)

/-- I(v): the finite set of edges incident with `v`. -/
def incidentEdges [Fintype E] [DecidableEq V] (v : V) : Finset E :=
  Finset.univ.filter (fun e : E => G.Incident e v)

/-- L(v): the finite set of loops at `v` (edges associated to {v}). -/
def loopsAt [Fintype E] [DecidableEq V] (v : V) : Finset E :=
  Finset.univ.filter (fun e : E => G.ends e = s(v, v))

/-- The other endpoint of an edge `e` at `v`: when `e` is incident with `v`, the vertex `u` with
`e` associated to {v, u} (so `u = v` for a loop). For edges not incident with `v` the value is
irrelevant; we use `v`. This is the "other element" of a two-element set, `Sym2.Mem.other`. -/
noncomputable def otherEnd [DecidableEq V] (v : V) (e : E) : V :=
  if h : v ∈ G.ends e then Sym2.Mem.other h else v

/-- If `e` is incident with `v`, then `e` is associated to {v, other endpoint}. -/
theorem ends_eq_of_incident [DecidableEq V] {v : V} {e : E} (h : G.Incident e v) :
    G.ends e = s(v, otherEnd G v e) := by
  -- unfold `otherEnd` at an incident edge, then use the defining property of `Sym2.Mem.other`
  have hmem : v ∈ G.ends e := h
  simp only [otherEnd, hmem, ↓reduceDIte]
  exact (Sym2.other_spec hmem).symm

/-- If `e` is associated to {v, u}, then its other endpoint at `v` is `u`. -/
theorem otherEnd_eq_of_ends {v w : V} {e : E} [DecidableEq V] (h : G.ends e = s(v, w)) :
    otherEnd G v e = w := by
  -- `e` is incident with `v`, so `e` is associated to {v, otherEnd}, and also to {v, w}
  have hinc : G.Incident e v := by
    change v ∈ G.ends e
    rw [h]
    exact Sym2.mem_mk_left v w
  have hboth : s(v, otherEnd G v e) = s(v, w) := (ends_eq_of_incident G hinc).symm.trans h
  -- cancel the common element `v`
  exact Sym2.congr_right.mp hboth

/-- **The degree splits.** deg v = |I(v)| + |L(v)|: every incident edge once, every loop again.
This is exactly the definition of `deg`. -/
theorem deg_eq [Fintype E] [DecidableEq V] (v : V) :
    G.deg v = (incidentEdges G v).card + (loopsAt G v).card := by
  rfl

/-- **Other endpoints of incident edges are exactly the neighbours.** The image of I(v) under the
other-endpoint map is N(v). -/
theorem image_otherEnd [Fintype V] [Fintype E] [DecidableEq V] (v : V) :
    (incidentEdges G v).image (otherEnd G v) = G.nbrFinset v := by
  ext w
  simp only [incidentEdges, UGraph.nbrFinset, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · -- an incident edge `e` joins `v` to its other endpoint `w`, so `v` and `w` are adjacent
    rintro ⟨e, hinc, rfl⟩
    exact ⟨e, ends_eq_of_incident G hinc⟩
  · -- an edge `e` joining `v` and `w` is incident with `v`, with other endpoint `w`
    rintro ⟨e, he⟩
    have hinc : G.Incident e v := by
      change v ∈ G.ends e
      rw [he]
      exact Sym2.mem_mk_left v w
    exact ⟨e, hinc, otherEnd_eq_of_ends G he⟩

/-- **Key characterization.** |N(v)| = deg v holds exactly when there are no loops at `v` and
different edges incident with `v` have different other endpoints.

The inequality |N(v)| ≤ |I(v)| ≤ deg v always holds; equality forces both steps to be equalities.
A loop makes the second step strict; two edges with the same other endpoint make the first
strict. -/
theorem card_nbr_eq_deg_iff [Fintype V] [Fintype E] [DecidableEq V] (v : V) :
    (G.nbrFinset v).card = G.deg v ↔
      (loopsAt G v).card = 0 ∧ Set.InjOn (otherEnd G v) (incidentEdges G v) := by
  -- |N(v)| is the size of the image of I(v) under the other-endpoint map
  have hN : (G.nbrFinset v).card = ((incidentEdges G v).image (otherEnd G v)).card := by
    rw [image_otherEnd]
  -- an image is never larger than the set it comes from: |N(v)| ≤ |I(v)|
  have hle : ((incidentEdges G v).image (otherEnd G v)).card ≤ (incidentEdges G v).card :=
    Finset.card_image_le
  -- the image has full size exactly when the map is one-to-one
  have hfull : ((incidentEdges G v).image (otherEnd G v)).card = (incidentEdges G v).card ↔
      Set.InjOn (otherEnd G v) (incidentEdges G v) :=
    Finset.card_image_iff
  rw [hN, deg_eq, ← hfull]
  -- now: |image| = |I(v)| + |L(v)| ↔ |L(v)| = 0 ∧ |image| = |I(v)|, using |image| ≤ |I(v)|
  omega

end Supp10b

open Supp10b

/-- **Supplementary Exercise 10(b).** "Let G = (V, E) be an undirected graph. Show that
|N(v)| = deg v for all v ∈ V if and only if G is a simple graph."

`[Fintype V] [Fintype E]` make deg v ("the number of edges incident with v") and |N(v)| finite
numbers; `[DecidableEq V]` is only needed to compute with `Finset.filter`. -/
theorem supp10b {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : UGraph V E) :
    (∀ v : V, (G.nbrFinset v).card = G.deg v) ↔ G.IsSimple := by
  constructor
  · -- (⇒) if |N(v)| = deg v everywhere, G has no loops and no multiple edges
    intro hEq
    -- no loops: a loop at `a` would lie in L(a), which must be empty
    have hNoLoops : ∀ e : E, ¬ G.IsLoop e := by
      intro e hloop
      -- a loop is associated to a one-element set {a}
      obtain ⟨a, ha⟩ : ∃ a : V, G.ends e = s(a, a) := by
        induction hends : G.ends e using Sym2.ind with
        | h x y =>
          rw [UGraph.IsLoop, hends, Sym2.mk_isDiag_iff] at hloop
          exact ⟨x, by rw [hloop]⟩
      -- so `e` is in L(a), making L(a) nonempty
      have heL : e ∈ loopsAt G a := by
        simp only [loopsAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ha
      -- but |N(a)| = deg a forces |L(a)| = 0
      have hL0 : (loopsAt G a).card = 0 := ((card_nbr_eq_deg_iff G a).mp (hEq a)).1
      rw [Finset.card_eq_zero] at hL0
      rw [hL0] at heL
      exact absurd heL (Finset.notMem_empty e)
    -- no multiple edges: two edges on the same {a, b} would share the other endpoint at `a`
    have hNoMultiple : ¬ G.HasMultipleEdges := by
      rintro ⟨e₁, e₂, hne, hsame⟩
      -- e₁ is associated to some set {a, b}
      obtain ⟨a, b, hab⟩ : ∃ a b : V, G.ends e₁ = s(a, b) := by
        induction hends : G.ends e₁ using Sym2.ind with
        | h x y => exact ⟨x, y, rfl⟩
      -- so is e₂
      have hab₂ : G.ends e₂ = s(a, b) := hsame.symm.trans hab
      -- both edges are incident with `a`
      have hinc : ∀ e : E, G.ends e = s(a, b) → e ∈ incidentEdges G a := by
        intro e he
        simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        change a ∈ G.ends e
        rw [he]
        exact Sym2.mem_mk_left a b
      -- both have other endpoint `b` at `a`
      have hsameOther : otherEnd G a e₁ = otherEnd G a e₂ := by
        rw [otherEnd_eq_of_ends G hab, otherEnd_eq_of_ends G hab₂]
      -- but |N(a)| = deg a forces the other-endpoint map to be one-to-one on I(a)
      have hInj : Set.InjOn (otherEnd G a) (incidentEdges G a) :=
        ((card_nbr_eq_deg_iff G a).mp (hEq a)).2
      exact hne (hInj (hinc e₁ hab) (hinc e₂ hab₂) hsameOther)
    exact ⟨hNoMultiple, hNoLoops⟩
  · -- (⇐) in a simple graph, |N(v)| = deg v for every v
    rintro ⟨hNoMultiple, hNoLoops⟩ v
    rw [card_nbr_eq_deg_iff]
    constructor
    · -- no loops at `v`: an edge associated to {v} would be a loop
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [loopsAt, Finset.mem_filter, Finset.mem_univ, true_and] at he
      apply hNoLoops e
      rw [UGraph.IsLoop, he]
      exact Sym2.mk_isDiag_iff.mpr rfl
    · -- two incident edges with the same other endpoint `u` are both associated to {v, u},
      -- so they are equal since there are no multiple edges
      intro e₁ h₁ e₂ h₂ hsameOther
      simp only [incidentEdges, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at h₁ h₂
      have hsameEnds : G.ends e₁ = G.ends e₂ := by
        rw [ends_eq_of_incident G h₁, ends_eq_of_incident G h₂, hsameOther]
      by_contra hne
      exact hNoMultiple ⟨e₁, e₂, hne, hsameEnds⟩

end GraphCh10
