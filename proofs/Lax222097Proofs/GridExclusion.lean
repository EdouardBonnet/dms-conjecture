import Lax222097.GridExclusion
import Lax222097.ColumnGridExclusion
import Lax222097.CycleObstruction
import Lax222097Proofs.InducedModels

namespace Lax222097Proofs

open Lax222097 ColumnGraph Grid Reduction CycleObstruction

/--
---
conclusion: Lax222097.ColumnGridExclusion.columnGraph_excludes_inducedGrid
---
Apply the general obstruction to the explicit triple of cycles in the grid.
-/
theorem columnGraph_excludes_inducedGrid (R : Type*) (c : ℕ) :
    ExcludesInducedGrid 5 (columnGraph R c) :=
  asteroidalCycles_obstruction R (Fin 5 × Fin 5) c (squareGrid 5)
    grid_five_has_asteroidalCycles

/--
---
conclusion: Lax222097.GridExclusion.reduction_excludes_inducedGrid
---
Induced-minor exclusion passes to induced subgraphs.
-/
theorem reduction_excludes_inducedGrid {n : ℕ} (F : SimpleGraph (Fin n)) :
    ExcludesInducedGrid 5 (reductionGraph F) := by
  rintro ⟨M⟩
  exact ColumnGridExclusion.columnGraph_excludes_inducedGrid (Reduction.Row F) (2 * n - 1)
    ⟨InducedModels.liftInduce M⟩

end Lax222097Proofs
