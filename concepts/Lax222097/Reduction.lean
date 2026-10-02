import Lax222097.ColumnGraph
import Lax222097.MaxCut

/-!
---
title: The Bonnet–Chang reduction
type: definition
---
Order the vertices of $F$ as $0,\ldots,n-1$. For every edge $uv$ with $u<v$,
reserve rows $(uv,0)$ and $(uv,1)$ in an intermediate graph with $2n-1$
columns. Keep only columns from $2u$ through $2v$. In row $(uv,t)$ keep
only side $t$ at column $2u$ and side $1-t$ at column $2v$; keep both sides
at every intervening column. The resulting induced subgraph is $G_F$.

The additive offset is $b(F)=2\sum_{uv\in E(F),\,u<v}(v-u)$.
-/

namespace Lax222097.Reduction

open ColumnGraph MaxCut

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

abbrev Row {n : ℕ} (F : SimpleGraph (Fin n)) := Edge F × Bool

abbrev Vertex {n : ℕ} (F : SimpleGraph (Fin n)) :=
  ColumnGraph.Vertex (Row F) (2 * n - 1)

def retainedVertices {n : ℕ} (F : SimpleGraph (Fin n)) : Set (Vertex F) :=
  fun ((edge, tag), column, side) =>
    let u := edge.val.1.val
    let v := edge.val.2.val
    let j := column.val
    (j = 2 * u ∧ side = tag) ∨
    (2 * u < j ∧ j < 2 * v) ∨
    (j = 2 * v ∧ side = !tag)

def reductionGraph {n : ℕ} (F : SimpleGraph (Fin n)) :
    SimpleGraph (retainedVertices F) :=
  (columnGraph (Row F) (2 * n - 1)).induce (retainedVertices F)

noncomputable def offset {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  2 * ∑ e ∈ edges F, (e.2.val - e.1.val)

end Lax222097.Reduction
