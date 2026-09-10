import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: The intermediate graph of rows, columns, and sides
type: definition
---
For any row set $R$ and $c$ columns, the intermediate graph has vertices
$(r,j,s)\in R\times\{0,\ldots,c-1\}\times\{0,1\}$. Each column induces a
complete bipartite graph between its two sides. Within a row, every vertex
is adjacent to both vertices in each consecutive column. There are no other
edges. With $|R|=2|E(F)|$ and $c=2|V(F)|-1$ this is Figure 1 of the paper.
-/

namespace Lax762056.ColumnGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

def graph (R : Type*) (c : ℕ) : SimpleGraph (Vertex R c) :=
  SimpleGraph.fromRel fun x y =>
    (x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
    (x.1 = y.1 ∧ (x.2.1.val + 1 = y.2.1.val ∨ y.2.1.val + 1 = x.2.1.val))

end Lax762056.ColumnGraph
