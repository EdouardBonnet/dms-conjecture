import Lax762056.Reduction
import Lax762056.Grid

/-!
---
title: The constructed graphs exclude the five-by-five grid
type: lemma
---
Claim 9: the intermediate graph excludes the $5\times5$ grid as an induced
minor. Therefore every reduction graph $G_F$, being an induced subgraph of
an intermediate graph, also excludes this induced minor.
-/

namespace Lax762056.GridExclusion

axiom intermediate (R : Type*) (c : ℕ) :
  Grid.ExcludesGrid (ColumnGraph.graph R c)

axiom reduction {n : ℕ} (F : SimpleGraph (Fin n)) :
  Grid.ExcludesGrid (Reduction.graph F)

end Lax762056.GridExclusion
