import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
---
title: Asteroidal triples of cycles
type: definition
---
An asteroidal triple of cycles consists of three vertex-disjoint, pairwise
nonadjacent cycles such that every pair is joined by a path avoiding the
closed neighborhood of the third.
-/

namespace Lax762056.AsteroidalCycles

open SimpleGraph

def AvoidsClosedNeighborhood {V : Type*} (G : SimpleGraph V)
    (S T : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y

def HasAsteroidalCycleTriple {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (base : Fin 3 → V) (cycle : ∀ i, Walk G (base i) (base i)),
    (∀ i, (cycle i).IsCycle) ∧
    (Pairwise fun i j => AvoidsClosedNeighborhood G
      {v | v ∈ (cycle i).support} {v | v ∈ (cycle j).support}) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∃ u ∈ (cycle i).support, ∃ v ∈ (cycle j).support,
        ∃ p : Path G u v, AvoidsClosedNeighborhood G
          {x | x ∈ p.val.support} {x | x ∈ (cycle k).support})

end Lax762056.AsteroidalCycles
