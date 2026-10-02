import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange
import Lax434930.PolynomialTime

/-!
---
title: Binary encoding of graph decision instances
type: definition
---
An instance consists of a finite simple graph on $\{0,\ldots,n-1\}$ and a
threshold $k$. Its encoding is $1^n0$, followed by the $n^2$ adjacency-matrix
bits in row order, followed by $1^k0$. Polynomial running time is measured
in the length of this word.
-/

namespace Lax222097.GraphEncoding

open scoped Classical

open List Turing Lax434930.PolynomialTime

/-- An input graph together with the requested solution-size threshold. -/
structure Instance where
  /-- The number of vertices. -/
  order : ℕ
  /-- A simple graph on vertices numbered from zero to `order - 1`. -/
  graph : SimpleGraph (Fin order)
  /-- The requested lower bound on the size of a solution. -/
  threshold : ℕ

/-- Encode a natural number as that many one-bits followed by a zero-bit. -/
def unary (n : ℕ) : Word := replicate n true ++ [false]

/-- Write the vertex count, the adjacency matrix row by row, and the threshold. -/
noncomputable def encode (I : Instance) : Word :=
  unary I.order ++
    (finRange I.order).flatMap (fun u =>
      (finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

/-- The instance transformation can be computed in polynomial time on these binary encodings. -/
def PolynomialTime (f : Instance → Instance) : Prop :=
  Nonempty (TM2ComputableInPolyTime encode encode f)

end Lax222097.GraphEncoding
