import Lax762056.Reduction

/-!
---
title: The reduction can be computed in polynomial time
type: lemma
---
The map $(F,k)\mapsto(G_F,k+b(F))$ can be computed in polynomial time.
The output vertices may be relabeled as consecutive integers.
-/

namespace Lax762056.ReductionTime

open GraphEncoding

axiom reduction_polynomial_time :
  ∃ f : Instance → Instance,
    PolynomialTime f ∧
    ∀ I, Nonempty ((f I).graph ≃g Reduction.graph I.graph) ∧
      (f I).threshold = I.threshold + Reduction.offset I.graph

end Lax762056.ReductionTime
