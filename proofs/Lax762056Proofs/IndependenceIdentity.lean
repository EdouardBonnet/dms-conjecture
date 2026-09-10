import Lax762056Proofs.IndependentUpper
import Lax762056Proofs.IndependentLower

namespace Lax762056Proofs

open Lax762056

/--
---
conclusion: Lax762056.IndependenceIdentity.identity
---
Every independent set induces a cut, with at most the stated number of
vertices in each edge's two rows. Conversely, the explicit construction
from a maximum cut realizes the bound, including the additional vertex
for each crossing edge.
-/
theorem independence_identity {n : ℕ} (F : SimpleGraph (Fin n)) :
    (Reduction.graph F).indepNum = MaxCut.maxCut F + Reduction.offset F :=
  Nat.le_antisymm IndependentUpper.independence_upper IndependentLower.independence_lower

end Lax762056Proofs
