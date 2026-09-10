import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Row and column graphs
type: definition
---
For a row set $R$ and $c$ columns, the graph has vertices
$(r,j,s)\in R\times\{0,\ldots,c-1\}\times\{0,1\}$. Each column induces a
complete bipartite graph between its two sides. Within a row, every vertex
is adjacent to both vertices in each consecutive column. There are no other
edges.
-/

namespace Lax762056.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

def columnGraph (R : Type*) (c : ℕ) : SimpleGraph (Vertex R c) :=
  fromRel fun (row, column, side) (row', column', side') =>
    (column = column' ∧ side ≠ side') ∨
    (row = row' ∧ (column.val + 1 = column'.val ∨ column'.val + 1 = column.val))

end Lax762056.ColumnGraph
