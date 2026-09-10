import Lax762056.Grid
import Lax762056.GraphProblems

/-!
---
title: Independent Set is NP-hard with an excluded grid
type: theorem
---
Maximum Independent Set is NP-hard on graphs
excluding the $5\times5$ grid as an induced minor.
In particular, deciding whether a graph in this class has an independent
set of size at least $k$ is NP-hard.
-/

namespace Lax762056.IndependentSetHardness

axiom independentSet_grid_hardness :
  GraphProblems.NPHardOn GraphProblems.IndependentSet Grid.ExcludesGrid

end Lax762056.IndependentSetHardness
