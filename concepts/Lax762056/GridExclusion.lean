import Lax762056.Reduction
import Lax762056.Grid

/-!
---
title: Excluding the 5×5 induced grid minor
type: lemma
---
Row and column graphs exclude the $5\times5$ grid as an induced minor.
The reduction graphs $G_F$ inherit this property as induced subgraphs.
-/

namespace Lax762056.GridExclusion

open ColumnGraph Grid Reduction

axiom columnGraph_excludes_inducedGrid (R : Type*) (c : ℕ) :
  ExcludesInducedGrid 5 (columnGraph R c)

axiom reduction_excludes_inducedGrid {n : ℕ} (F : SimpleGraph (Fin n)) :
  ExcludesInducedGrid 5 (reductionGraph F)

end Lax762056.GridExclusion
