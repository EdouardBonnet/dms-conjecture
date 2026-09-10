import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: Induced minors
type: definition
---
A graph $H$ is an induced minor of $G$ if its vertices have pairwise disjoint,
nonempty connected branch sets in $G$, and two distinct branch sets are joined
by an edge exactly when their vertices are adjacent in $H$. Thus edges between
retained branch sets cannot be deleted. For finite graphs this is the usual
definition by vertex deletions and edge contractions.
-/

namespace Lax762056.InducedMinors

structure Model {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  connected : ∀ v, (G.induce (branch v)).Connected
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  adjacent : ∀ u v, u ≠ v →
    (H.Adj u v ↔ ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y)

def IsInducedMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax762056.InducedMinors
