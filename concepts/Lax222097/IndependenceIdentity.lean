import Lax222097.Reduction

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

namespace Lax222097.IndependenceIdentity

open Reduction MaxCut

axiom independence_eq_maxCut_offset {n : ℕ} (F : SimpleGraph (Fin n)) :
  (reductionGraph F).indepNum = maxCut F + offset F

end Lax222097.IndependenceIdentity
