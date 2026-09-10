import Lax762056.GridExclusion
import Lax762056.CycleObstruction
import Lax762056Proofs.InducedModels

namespace Lax762056Proofs

open Lax762056 ColumnGraph Grid Reduction CycleObstruction

/--
---
conclusion: Lax762056.GridExclusion.columnGraph_excludes_inducedGrid
---
Apply the general obstruction to the explicit triple of cycles in the grid.
-/
theorem columnGraph_excludes_inducedGrid (R : Type*) (c : ℕ) :
    ExcludesInducedGrid 5 (columnGraph R c) :=
  asteroidalCycles_obstruction R (Fin 5 × Fin 5) c (squareGrid 5)
    grid_five_has_asteroidalCycles

/--
---
conclusion: Lax762056.GridExclusion.reduction_excludes_inducedGrid
---
Induced-minor exclusion passes to induced subgraphs.
-/
theorem reduction_excludes_inducedGrid {n : ℕ} (F : SimpleGraph (Fin n)) :
    ExcludesInducedGrid 5 (reductionGraph F) := by
  rintro ⟨M⟩
  exact GridExclusion.columnGraph_excludes_inducedGrid (Reduction.Row F) (2 * n - 1)
    ⟨InducedModels.liftInduce M⟩

end Lax762056Proofs
