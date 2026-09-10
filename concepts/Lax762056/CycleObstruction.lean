import Lax762056.AsteroidalCycles
import Lax762056.ColumnGraph
import Lax762056.Grid

/-!
---
title: Asteroidal cycles obstruct induced minors
type: lemma
---
Every cycle in an intermediate graph contains vertices on opposite sides of
one column. Their joint closed neighborhood contains that entire column. Consequently,
a graph with three mutually avoiding cycles cannot be an induced minor of
an intermediate graph. The $5\times5$ grid contains such a triple.
-/

namespace Lax762056.CycleObstruction

axiom avoidingCycles_obstruction (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : AsteroidalCycles.HasAsteroidalTriple H) :
  ¬ InducedMinors.IsInducedMinor H (ColumnGraph.graph R c)

axiom grid_has_avoidingCycles : AsteroidalCycles.HasAsteroidalTriple Grid.fiveByFiveGrid

end Lax762056.CycleObstruction
