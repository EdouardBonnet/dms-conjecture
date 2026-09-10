import Lax762056.GridExclusion
import Lax762056Proofs.GridWitness
import Lax762056Proofs.Obstruction

namespace Lax762056Proofs

open Lax762056

/--
---
conclusion: Lax762056.GridExclusion.columnGraph_excludes_grid
---
Apply the general obstruction to the explicit triple of cycles in the grid.
-/
theorem columnGraph_excludes_grid (R : Type*) (c : ℕ) :
    Grid.ExcludesGrid (ColumnGraph.graph R c) :=
  Obstruction.avoidingCycles_obstruction R (Fin 5 × Fin 5) c Grid.fiveByFiveGrid GridWitness.grid_has_avoidingCycles

/--
---
conclusion: Lax762056.GridExclusion.reduction_excludes_grid
---
Induced-minor exclusion passes to induced subgraphs.
-/
theorem reduction_excludes_grid {n : ℕ} (F : SimpleGraph (Fin n)) :
    Grid.ExcludesGrid (Reduction.graph F) := by
  rintro ⟨M⟩
  exact columnGraph_excludes_grid (Reduction.Row F) (2 * n - 1)
    ⟨InducedModels.liftInduce M⟩

end Lax762056Proofs
