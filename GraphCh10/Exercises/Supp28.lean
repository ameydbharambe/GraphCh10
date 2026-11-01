-- STATUS: COMPLETE

import GraphCh10.Definitions
import GraphCh10.Lemmas

/-!
# Supplementary Exercise 28

**Answer: the assertion is false.**

Paper proof (counterexample). Inside the ambient vertex set {0, 1, 2, 3}, let
* G₁ = G₂ = H₁ = K₂ on {0, 1}  (vertices {0, 1}, one edge {0, 1}),
* H₂ = K₂ on {2, 3}             (vertices {2, 3}, one edge {2, 3}).

1. G₁ and H₁ are the same graph, so they are isomorphic (the identity is an isomorphism).
2. G₂ and H₂ are isomorphic by v ↦ v + 2, which sends 0 ↦ 2, 1 ↦ 3 and the edge {0, 1} to the
   edge {2, 3}.
3. G₁ ∪ G₂ = ({0, 1}, {{0, 1}}) has 2 vertices, while
   H₁ ∪ H₂ = ({0, 1, 2, 3}, {{0, 1}, {2, 3}}) has 4 vertices.
4. An isomorphism is in particular a one-to-one correspondence between the vertex sets, so
   isomorphic graphs have the same number of vertices. Hence G₁ ∪ G₂ and H₁ ∪ H₂ are not
   isomorphic, and the assertion fails for this choice of graphs.
-/

namespace GraphCh10

universe u v

namespace Supp28

/-! ## The two copies of K₂ -/

/-- K₂ on the vertices {0, 1} inside `Fin 4`. -/
def k2Low : SetSimpleGraph (Fin 4) where
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
    -- {0, 1} is not a loop because 0 ≠ 1
    decide

/-- K₂ on the vertices {2, 3} inside `Fin 4`. -/
def k2High : SetSimpleGraph (Fin 4) where
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
    -- {2, 3} is not a loop because 2 ≠ 3
    decide

/-! ## Helper facts -/

/-- Every simple graph is isomorphic to itself: the identity map on V is a one-to-one
correspondence that sends each pair {v₁, v₂} to itself. -/
theorem isomorphic_refl {α : Type u} (G : SetSimpleGraph α) : G.Isomorphic G := by
  -- the identity is the required one-to-one correspondence
  refine ⟨Equiv.refl G.V, ?_⟩
  -- it maps {v₁, v₂} to {v₁, v₂}, so the edge condition is `p ↔ p`
  intro v₁ v₂
  exact Iff.rfl

/-- Isomorphic simple graphs have the same number of vertices. Stated for graphs whose vertex sets
are given by explicit finite sets `s` and `t`: an isomorphism contains a one-to-one correspondence
V₁ → V₂, so `s` and `t` have the same number of elements. -/
theorem card_eq_of_isomorphic {α : Type u} {β : Type v}
    {G : SetSimpleGraph α} {H : SetSimpleGraph β} {s : Finset α} {t : Finset β}
    (hG : G.V = ↑s) (hH : H.V = ↑t) (hiso : G.Isomorphic H) : s.card = t.card := by
  -- the one-to-one correspondence V₁ → V₂ underlying the isomorphism
  obtain ⟨f, -⟩ := hiso
  -- composing with V₁ = s and V₂ = t gives a one-to-one correspondence s → t
  have eG : G.V ≃ (↑s : Set α) := Equiv.subtypeEquivRight (fun x => by rw [hG])
  have eH : H.V ≃ (↑t : Set β) := Equiv.subtypeEquivRight (fun x => by rw [hH])
  have e : (↑s : Set α) ≃ (↑t : Set β) := eG.symm.trans (f.trans eH)
  -- finite sets in one-to-one correspondence have the same number of elements
  calc s.card = Fintype.card (↑s : Set α) := (Fintype.card_coe s).symm
    _ = Fintype.card (↑t : Set β) := Fintype.card_congr e
    _ = t.card := Fintype.card_coe t

/-- G₁ and G₂ (both K₂ on {0, 1}) are isomorphic to H₂ = K₂ on {2, 3}, via v ↦ v + 2. -/
theorem k2Low_isomorphic_k2High : k2Low.Isomorphic k2High := by
  -- the bijection {0, 1} → {2, 3}, v ↦ v + 2, with inverse w ↦ w − 2
  let f : k2Low.V ≃ k2High.V :=
    { toFun := fun x => ⟨x.1 + 2, by
        rcases x with ⟨x, hx⟩
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl⟩
      invFun := fun y => ⟨y.1 - 2, by
        rcases y with ⟨y, hy⟩
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        rcases hx with rfl | rfl <;> rfl
      right_inv := by
        rintro ⟨y, hy⟩
        apply Subtype.ext
        rcases hy with rfl | rfl <;> rfl }
  refine ⟨f, ?_⟩
  -- check the edge condition on all four ordered pairs of vertices of {0, 1}
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  change s(x + 2, y + 2) ∈ ({s(2, 3)} : Set (Sym2 (Fin 4))) ↔
    s(x, y) ∈ ({s(0, 1)} : Set (Sym2 (Fin 4)))
  simp only [Set.mem_singleton_iff]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

/-- G₁ ∪ G₂ = K₂ ∪ K₂ (both on {0, 1}) has vertex set {0, 1}. -/
theorem union_low_low_V : (k2Low ∪ k2Low).V = ↑({0, 1} : Finset (Fin 4)) := by
  -- V₁ ∪ V₂ = {0, 1} ∪ {0, 1} = {0, 1}
  change ({0, 1} : Set (Fin 4)) ∪ {0, 1} = ↑({0, 1} : Finset (Fin 4))
  rw [Set.union_self, Finset.coe_insert, Finset.coe_singleton]

/-- H₁ ∪ H₂ = (K₂ on {0, 1}) ∪ (K₂ on {2, 3}) has vertex set {0, 1, 2, 3}. -/
theorem union_low_high_V : (k2Low ∪ k2High).V = ↑({0, 1, 2, 3} : Finset (Fin 4)) := by
  -- V₁ ∪ V₂ = {0, 1} ∪ {2, 3} = {0, 1, 2, 3}
  change ({0, 1} : Set (Fin 4)) ∪ {2, 3} = ↑({0, 1, 2, 3} : Finset (Fin 4))
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert,
    Finset.coe_singleton]
  tauto

end Supp28

open Supp28 in
/-- **Supplementary Exercise 28.** Suppose that G₁ and H₁ are isomorphic and that G₂ and H₂ are
isomorphic. Prove or disprove that G₁ ∪ G₂ and H₁ ∪ H₂ are isomorphic.

**Answer: disproved.** The universal statement is false; see the counterexample in the module
docstring. -/
theorem supp28 :
    ¬ ∀ (α β : Type)
        (G₁ G₂ : SetSimpleGraph α)
        (H₁ H₂ : SetSimpleGraph β),
        G₁.Isomorphic H₁ →
        G₂.Isomorphic H₂ →
        (G₁ ∪ G₂).Isomorphic (H₁ ∪ H₂) := by
  intro hall
  -- G₁ = H₁ = K₂ on {0, 1}, so G₁ ≅ H₁ by the identity
  have h₁ : k2Low.Isomorphic k2Low := isomorphic_refl k2Low
  -- G₂ = K₂ on {0, 1} and H₂ = K₂ on {2, 3} are isomorphic via v ↦ v + 2
  have h₂ : k2Low.Isomorphic k2High := k2Low_isomorphic_k2High
  -- the assertion would then make G₁ ∪ G₂ and H₁ ∪ H₂ isomorphic
  have hunion : (k2Low ∪ k2Low).Isomorphic (k2Low ∪ k2High) :=
    hall (Fin 4) (Fin 4) k2Low k2Low k2Low k2High h₁ h₂
  -- so their vertex sets {0, 1} and {0, 1, 2, 3} would have equally many elements
  have hcard : ({0, 1} : Finset (Fin 4)).card = ({0, 1, 2, 3} : Finset (Fin 4)).card :=
    card_eq_of_isomorphic union_low_low_V union_low_high_V hunion
  -- but the first has 2 elements and the second has 4
  have h2 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have h4 : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  -- 2 ≠ 4, a contradiction
  rw [h2, h4] at hcard
  exact absurd hcard (by decide)

end GraphCh10
