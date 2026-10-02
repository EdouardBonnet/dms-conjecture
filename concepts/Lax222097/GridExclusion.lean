import Lax222097.Reduction
import Lax222097.Grid

/-!
---
title: Induced grid exclusion in the reduction
type: lemma
---
For every finite simple graph $F$, the reduction graph $G_F$ excludes
the $5\times5$ grid as an induced minor.
-/

namespace Lax222097.GridExclusion

open Grid Reduction

axiom reduction_excludes_inducedGrid {n : ℕ} (F : SimpleGraph (Fin n)) :
  ExcludesInducedGrid 5 (reductionGraph F)

end Lax222097.GridExclusion
