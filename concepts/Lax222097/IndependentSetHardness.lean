import Lax222097.Grid
import Lax222097.GraphProblems

/-!
---
title: Independent Set without a 5×5 induced grid minor
type: theorem
---
Deciding whether a graph has an independent set of size at least $k$ is
NP-hard even when the graph excludes the $5\times5$ grid as an induced minor.
Consequently, Maximum Independent Set is NP-hard on this class.
-/

namespace Lax222097.IndependentSetHardness

open GraphProblems Grid

axiom independentSet_inducedGrid_hardness :
  NPHardOn IndependentSet (ExcludesInducedGrid 5)

end Lax222097.IndependentSetHardness
