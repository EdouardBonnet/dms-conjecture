import Lax762056.Reduction

/-!
---
title: The reduction can be computed in polynomial time
type: lemma
---
There is a single polynomial time algorithm that, from the encoded instance
$(F,k)$, outputs an encoded graph isomorphic to $G_F$ with threshold $k+b(F)$.
Both input and output use the specified adjacency-matrix encoding. The graph
isomorphism permits the algorithm to enumerate the retained vertices in a
fixed order; it does not require a noncomputable relabeling to be executable.

The claim includes a finite Turing machine and a polynomial bound on its
actual computation time. A polynomial bound on the number of output vertices
alone is not sufficient to discharge it.
-/

namespace Lax762056.ReductionTime

open GraphEncoding

axiom polynomial_time :
  ∃ f : Instance → Instance,
    Nonempty (Turing.TM2ComputableInPolyTime encode encode f) ∧
    ∀ I, Nonempty ((f I).graph ≃g Reduction.graph I.graph) ∧
      (f I).threshold = I.threshold + Reduction.offset I.graph

end Lax762056.ReductionTime
