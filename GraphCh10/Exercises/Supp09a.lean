-- STATUS: COMPLETE


import GraphCh10.Definitions

/-!
# Supplementary Exercise 9(a)
-/

namespace GraphCh10

universe u v

/-- **Supplementary Exercise 9(a).** "Let G = (V, E) be an undirected graph and let A ⊆ V and
B ⊆ V. Show that a) N(A ∪ B) = N(A) ∪ N(B)."

No hypotheses beyond the problem text: N(A) is meaningful for any undirected graph,
finite or not. -/
theorem supp09a {V : Type u} {E : Type v} (G : UGraph V E) (A B : Set V) :
    G.nbhdSet (A ∪ B) = G.nbhdSet A ∪ G.nbhdSet B := by
  -- two sets are equal when they have the same elements, so fix a vertex `u`
  ext u
  -- (⊆) a vertex adjacent to some vertex of A ∪ B is adjacent to a vertex of A or a vertex of B
  have forward : u ∈ G.nbhdSet (A ∪ B) → u ∈ G.nbhdSet A ∪ G.nbhdSet B := by
    rintro ⟨a, haAB, hadj⟩
    -- the witness `a` lies in A or in B
    rcases haAB with haA | haB
    · -- `a ∈ A`, so `u ∈ N(A)`
      exact Or.inl ⟨a, haA, hadj⟩
    · -- `a ∈ B`, so `u ∈ N(B)`
      exact Or.inr ⟨a, haB, hadj⟩
  -- (⊇) a vertex adjacent to a vertex of A, or to a vertex of B, is adjacent to a vertex of A ∪ B
  have backward : u ∈ G.nbhdSet A ∪ G.nbhdSet B → u ∈ G.nbhdSet (A ∪ B) := by
    rintro (⟨a, haA, hadj⟩ | ⟨b, hbB, hadj⟩)
    · -- a witness in A is also a witness in A ∪ B
      exact ⟨a, Or.inl haA, hadj⟩
    · -- a witness in B is also a witness in A ∪ B
      exact ⟨b, Or.inr hbB, hadj⟩
  -- combine both inclusions
  exact ⟨forward, backward⟩

end GraphCh10
