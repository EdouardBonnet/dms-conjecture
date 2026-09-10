import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax762056.InducedMinors

/-!
---
title: Excluding the five-by-five grid as an induced minor
type: definition
---
The $5\times5$ grid is the Cartesian product of two five-vertex paths.
Grid exclusion is the absence of this graph as an induced minor.
-/

namespace Lax762056.Grid

def fiveByFiveGrid : SimpleGraph (Fin 5 × Fin 5) :=
  (SimpleGraph.pathGraph 5).boxProd (SimpleGraph.pathGraph 5)

def ExcludesGrid {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ InducedMinors.IsInducedMinor fiveByFiveGrid G

end Lax762056.Grid
