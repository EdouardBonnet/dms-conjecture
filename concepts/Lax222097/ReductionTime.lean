import Lax222097.Reduction

/-!
---
title: The reduction can be computed in polynomial time
type: lemma
---
The map $(F,k)\mapsto(G_F,k+b(F))$ can be computed in polynomial time.
The output vertices may be relabeled as consecutive integers.
-/

namespace Lax222097.ReductionTime

open GraphEncoding Reduction

axiom reduction_polynomial_time :
  ∃ f : Instance → Instance,
    PolynomialTime f ∧
    ∀ I, Nonempty ((f I).graph ≃g reductionGraph I.graph) ∧
      (f I).threshold = I.threshold + offset I.graph

end Lax222097.ReductionTime
