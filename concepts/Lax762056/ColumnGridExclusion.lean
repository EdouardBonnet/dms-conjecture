import Lax762056.ColumnGraph
import Lax762056.Grid

/-!
---
title: Induced grid exclusion in row and column graphs
type: lemma
---
Every row and column graph excludes the $5\times5$ grid as an induced minor.
-/

namespace Lax762056.ColumnGridExclusion

open ColumnGraph Grid

axiom columnGraph_excludes_inducedGrid (R : Type*) (c : ℕ) :
  ExcludesInducedGrid 5 (columnGraph R c)

end Lax762056.ColumnGridExclusion
