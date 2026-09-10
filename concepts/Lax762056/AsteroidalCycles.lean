import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
---
title: Three mutually avoiding cycles
type: definition
---
A graph has three mutually avoiding cycles if it contains three vertex-disjoint,
pairwise nonadjacent cycles, and between any two there is a path avoiding
the closed neighborhood of the third. A walk suffices in the formal
definition, since deleting repeated portions gives a path with the same
avoidance property. This is the obstruction used in the proof of Claim 9.
-/

namespace Lax762056.AsteroidalCycles

def HasTriple {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (base : Fin 3 → V) (cycle : ∀ i, G.Walk (base i) (base i)),
    (∀ i, (cycle i).IsCycle) ∧
    (∀ i j, i ≠ j → ∀ u ∈ (cycle i).support, ∀ v ∈ (cycle j).support,
      u ≠ v ∧ ¬ G.Adj u v) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∃ u ∈ (cycle i).support, ∃ v ∈ (cycle j).support,
        ∃ p : G.Walk u v, ∀ x ∈ p.support, ∀ y ∈ (cycle k).support,
          x ≠ y ∧ ¬ G.Adj x y)

end Lax762056.AsteroidalCycles
