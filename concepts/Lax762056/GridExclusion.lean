import Lax762056.Reduction
import Lax762056.Grid

/-!
---
title: The constructed graphs exclude the five-by-five grid
type: lemma
---
Row and column graphs exclude the $5\times5$ grid as an induced minor.
The reduction graphs $G_F$ inherit this property as induced subgraphs.
-/

namespace Lax762056.GridExclusion

axiom columnGraph_excludes_grid (R : Type*) (c : ℕ) :
  Grid.ExcludesGrid (ColumnGraph.graph R c)

axiom reduction_excludes_grid {n : ℕ} (F : SimpleGraph (Fin n)) :
  Grid.ExcludesGrid (Reduction.graph F)

end Lax762056.GridExclusion
