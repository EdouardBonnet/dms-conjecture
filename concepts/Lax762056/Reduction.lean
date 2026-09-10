import Lax762056.ColumnGraph
import Lax762056.MaxCut

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

Column $2j$ here is column $2(j+1)-1$ in the paper's indexing. Labeling rows
by their edges avoids making an arbitrary choice of an edge ordering. The
additive offset is $b(F)=2\sum_{uv\in E(F),\,u<v}(v-u)$.
-/

namespace Lax762056.Reduction

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

abbrev Row {n : ℕ} (F : SimpleGraph (Fin n)) := Edge F × Bool

abbrev Vertex {n : ℕ} (F : SimpleGraph (Fin n)) :=
  ColumnGraph.Vertex (Row F) (2 * n - 1)

def kept {n : ℕ} (F : SimpleGraph (Fin n)) : Set (Vertex F) :=
  {x | let u := x.1.1.val.1.val
       let v := x.1.1.val.2.val
       let t := x.1.2
       let j := x.2.1.val
       let s := x.2.2
       (j = 2 * u ∧ s = t) ∨
       (2 * u < j ∧ j < 2 * v) ∨
       (j = 2 * v ∧ s = !t)}

def graph {n : ℕ} (F : SimpleGraph (Fin n)) : SimpleGraph (kept F) :=
  (ColumnGraph.graph (Row F) (2 * n - 1)).induce (kept F)

noncomputable def offset {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  2 * ∑ e ∈ MaxCut.edges F, (e.2.val - e.1.val)

end Lax762056.Reduction
