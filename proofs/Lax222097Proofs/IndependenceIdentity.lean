import Lax222097Proofs.IndependentUpper
import Lax222097Proofs.IndependentLower

namespace Lax222097Proofs

open Lax222097 MaxCut Reduction

/--
---
conclusion: Lax222097.IndependenceIdentity.independence_eq_maxCut_offset
---
Every independent set induces a cut, with at most the stated number of
vertices in each edge's two rows. Conversely, the explicit construction
from a maximum cut realizes the bound, including the additional vertex
for each crossing edge.
-/
theorem independence_eq_maxCut_offset {n : ℕ} (F : SimpleGraph (Fin n)) :
    (reductionGraph F).indepNum = maxCut F + offset F :=
  Nat.le_antisymm IndependentUpper.independence_upper IndependentLower.independence_lower

end Lax222097Proofs
