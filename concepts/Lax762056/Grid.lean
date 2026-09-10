import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax762056.InducedMinors

/-!
---
title: Excluded induced grid minors
type: definition
---
The $k\times k$ square grid is the Cartesian product of two $k$-vertex paths.
A graph excludes the induced grid of size $k$ if this square grid is not
an induced minor of the graph.
-/

namespace Lax762056.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

def ExcludesInducedGrid (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsInducedMinor (squareGrid k) G

end Lax762056.Grid
