import Lax762056.GridExclusion
import Lax762056Proofs.GridWitness
import Lax762056Proofs.Obstruction

namespace Lax762056Proofs

open Lax762056

/--
---
conclusion: Lax762056.GridExclusion.intermediate
---
Apply the general obstruction to the explicit triple of cycles in the grid.
-/
theorem intermediate_excludes_grid (R : Type*) (c : ℕ) :
    Grid.ExcludesGrid (ColumnGraph.graph R c) :=
  Obstruction.excludes_triple R (Fin 5 × Fin 5) c Grid.grid GridWitness.grid_has_triple

/--
---
conclusion: Lax762056.GridExclusion.reduction
---
An induced-minor model in the retained graph lifts to its intermediate
graph simply by viewing its branch sets in the original vertex type.
-/
theorem reduction_excludes_grid {n : ℕ} (F : SimpleGraph (Fin n)) :
    Grid.ExcludesGrid (Reduction.graph F) := by
  rintro ⟨M⟩
  exact intermediate_excludes_grid (Reduction.Row F) (2 * n - 1)
    ⟨InducedModels.liftInduce M⟩

end Lax762056Proofs
