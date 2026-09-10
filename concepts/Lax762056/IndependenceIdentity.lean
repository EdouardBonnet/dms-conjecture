import Lax762056.Reduction

/-!
---
title: The independence number records the maximum cut
type: lemma
---
For every finite simple graph $F$,
$\alpha(G_F)=\operatorname{MaxCut}(F)+b(F)$.
An independent set chooses at most one side in each column and so determines
a cut of $F$ (empty columns may be assigned either side). The two rows for
an edge $uv$ contribute at most $2(v-u)+1$ vertices, and at most $2(v-u)$
when its endpoints lie on the same side. Conversely, every cut realizes
the sum of these bounds.
-/

namespace Lax762056.IndependenceIdentity

axiom independence_eq_maxCut_offset {n : ℕ} (F : SimpleGraph (Fin n)) :
  (Reduction.graph F).indepNum = MaxCut.maxCut F + Reduction.offset F

end Lax762056.IndependenceIdentity
