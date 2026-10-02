import Lax222097.AsteroidalCycles
import Lax222097.ColumnGraph
import Lax222097.Grid

/-!
---
title: Asteroidal cycle triples obstruct induced minors
type: lemma
---
No graph containing an asteroidal triple of cycles is an induced minor of
a row and column graph. The $5\times5$ grid contains such a triple.
-/

namespace Lax222097.CycleObstruction

open AsteroidalCycles ColumnGraph Grid InducedMinors

axiom asteroidalCycles_obstruction (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : HasAsteroidalCycleTriple H) :
  ¬ IsInducedMinor H (columnGraph R c)

axiom grid_five_has_asteroidalCycles : HasAsteroidalCycleTriple (squareGrid 5)

end Lax222097.CycleObstruction
