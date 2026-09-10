import Lax762056.AsteroidalCycles
import Lax762056.ColumnGraph
import Lax762056.Grid

/-!
---
title: The cycle obstruction to an induced minor
type: lemma
---
Every cycle in an intermediate graph contains vertices on opposite sides of
one column. Their joint neighborhood contains that entire column. Consequently,
a graph with three mutually avoiding cycles cannot be an induced minor of
an intermediate graph. The $5\times5$ grid has such a triple (Figure 4).

These are the two structural ingredients of Claim 9. The obstruction is
stated for every intermediate graph, independently of the Max Cut instance.
-/

namespace Lax762056.CycleObstruction

axiom excludes_triple (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : AsteroidalCycles.HasTriple H) :
  ¬ InducedMinors.IsInducedMinor H (ColumnGraph.graph R c)

axiom grid_has_triple : AsteroidalCycles.HasTriple Grid.grid

end Lax762056.CycleObstruction
