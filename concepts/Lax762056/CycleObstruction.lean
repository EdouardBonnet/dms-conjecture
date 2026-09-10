import Lax762056.AsteroidalCycles
import Lax762056.ColumnGraph
import Lax762056.Grid

/-!
---
title: Asteroidal cycle triples obstruct induced minors
type: lemma
---
No graph containing an asteroidal triple of cycles is an induced minor of
a row and column graph. The $5\times5$ grid contains such a triple.
-/

namespace Lax762056.CycleObstruction

open AsteroidalCycles ColumnGraph Grid InducedMinors

axiom asteroidalCycles_obstruction (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : HasAsteroidalCycleTriple H) :
  ¬ IsInducedMinor H (columnGraph R c)

axiom grid_five_has_asteroidalCycles : HasAsteroidalCycleTriple (squareGrid 5)

end Lax762056.CycleObstruction
