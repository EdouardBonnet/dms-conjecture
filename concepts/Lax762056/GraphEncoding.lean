import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange
import Lax434930.PolynomialTime

/-!
---
title: Binary encoding of graph decision instances
type: definition
---
An instance is a finite simple graph on $\{0,\ldots,n-1\}$ and a natural
threshold $k$. Its encoding is $1^n0$, followed by the $n^2$ adjacency-matrix
bits in row order, followed by $1^k0$. This includes the empty graph and
threshold zero, and uniquely specifies the entire instance.

Unary thresholds suffice for both problems: thresholds exceeding the number
of vertices for Independent Set, or the number of edges for Max Cut, can be
rejected immediately. On the remaining inputs this encoding is polynomially
equivalent to the usual binary-threshold encoding.

Polynomial time is measured in the length of this explicit binary encoding,
using the same finite Turing machines as the archive's definitions of P and
NP. Choosing truth values of the finitely many adjacency propositions below
does not posit an algorithm or a time bound; those are separate obligations.
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

end Lax762056.GraphEncoding
