import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax762056.InducedMinors

/-!
---
title: Excluding the five-by-five grid as an induced minor
type: definition
---
The $5\times5$ grid has vertex set $\{0,\ldots,4\}^2$, with adjacency between
orthogonally consecutive positions. We use mathlib's Cartesian product of
two five-vertex paths. A graph belongs to the class in Theorem 5 precisely
when this grid is not its induced minor.
-/

namespace Lax762056.Grid

def grid : SimpleGraph (Fin 5 × Fin 5) :=
  (SimpleGraph.pathGraph 5).boxProd (SimpleGraph.pathGraph 5)

def ExcludesGrid {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ InducedMinors.IsInducedMinor grid G

end Lax762056.Grid
