-- STATUS: COMPLETE

import GraphCh10.Definitions
import GraphCh10.DefinitionTests

/-!
# Supplementary Exercise 8

**Answer: the statement is false.** A counterexample is the multigraph `Tests.ex8` on the
vertices {0, 1, 2}, with edges {0,1}, {1,2}, {1,2} (the last two are parallel edges). It has
no loops and three vertices, but its degrees are deg(0) = 1, deg(1) = 3, deg(2) = 2, which are
pairwise different.
-/

namespace GraphCh10

open GraphCh10.Tests

/-- **Supplementary Exercise 8.** "Prove or disprove that there are always two vertices of the
same degree in a finite multigraph having at least two vertices."

We disprove it: the negation of the universal statement holds. Finiteness of the multigraph is
expressed by `[Fintype V] [Fintype E]` (finitely many vertices and edges); `[DecidableEq V]` is
only needed to compute degrees. -/
theorem supp08 :
    ¬ ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V]
        (G : UGraph V E),
        G.IsMultigraph → 2 ≤ Fintype.card V →
        ∃ u w : V, u ≠ w ∧ G.deg u = G.deg w := by
  -- assume, for contradiction, that every such multigraph has two vertices of equal degree
  intro claim
  -- the counterexample `ex8` has no loops, so it is a multigraph
  have hMulti : ex8.IsMultigraph := by
    unfold UGraph.IsMultigraph UGraph.IsLoop
    decide
  -- it has three vertices, so at least two
  have hCard : 2 ≤ Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    decide
  -- its degrees are deg(0) = 1, deg(1) = 3, deg(2) = 2
  have hDeg : ex8.deg 0 = 1 ∧ ex8.deg 1 = 3 ∧ ex8.deg 2 = 2 := by
    decide
  -- hence any two distinct vertices of `ex8` have different degrees
  have hDistinct : ∀ u w : Fin 3, u ≠ w → ex8.deg u ≠ ex8.deg w := by
    intro u w hne
    obtain ⟨h0, h1, h2⟩ := hDeg
    -- check all ordered pairs of vertices, using the three degrees above
    match u, w with
    | 0, 0 => exact absurd rfl hne
    | 0, 1 => rw [h0, h1]; decide
    | 0, 2 => rw [h0, h2]; decide
    | 1, 0 => rw [h1, h0]; decide
    | 1, 1 => exact absurd rfl hne
    | 1, 2 => rw [h1, h2]; decide
    | 2, 0 => rw [h2, h0]; decide
    | 2, 1 => rw [h2, h1]; decide
    | 2, 2 => exact absurd rfl hne
  -- but the assumed claim, applied to `ex8`, gives two distinct vertices of equal degree
  obtain ⟨u, w, hne, hEq⟩ := claim (Fin 3) (Fin 3) ex8 hMulti hCard
  -- contradiction
  exact hDistinct u w hne hEq

end GraphCh10
