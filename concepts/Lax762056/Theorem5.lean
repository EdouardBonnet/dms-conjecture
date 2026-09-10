import Lax762056.Grid
import Lax762056.GraphEncoding
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: MIS is NP-hard when excluding the five-by-five grid as an induced minor
type: theorem
---
**Theorem 5 (Bonnet–Chang).** Maximum Independent Set is NP-hard on graphs
excluding the $5\times5$ grid as an induced minor.

Precisely, for every binary language $A$ in the archive's NP there is one
polynomial time reduction sending every word $x$ to a finite simple graph
$G_x$ and threshold $k_x$. Every $G_x$ excludes the grid as an induced minor,
and $x\in A$ if and only if $\alpha(G_x)\ge k_x$. The class restriction holds
on both yes- and no-inputs. The graph class need not be recognized by the
Independent Set algorithm.

This decision formulation also implies hardness of computing the maximum
independent-set size or an actual maximum independent set. The theorem has
no assumption that Max Cut is hard, no assumption about the reduction, and
no assumption separating complexity classes.
-/

namespace Lax762056.Theorem5

open GraphEncoding
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

axiom np_hard (A : Language) (hA : A ∈ NP) :
  ∃ f : Word → Instance,
    Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
    ∀ x, Grid.ExcludesGrid (f x).graph ∧
      (x ∈ A ↔ (f x).threshold ≤ (f x).graph.indepNum)

end Lax762056.Theorem5
