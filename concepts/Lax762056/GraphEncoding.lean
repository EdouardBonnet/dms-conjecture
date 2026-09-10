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

namespace Lax762056.GraphEncoding

open Lax434930.PolynomialTime

structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  threshold : ℕ

def unary (n : ℕ) : Word := List.replicate n true ++ [false]

noncomputable def encode (I : Instance) : Word := by
  classical
  exact unary I.order ++
    (List.finRange I.order).flatMap (fun u =>
      (List.finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

def PolynomialTime (f : Instance → Instance) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encode encode f)

end Lax762056.GraphEncoding
