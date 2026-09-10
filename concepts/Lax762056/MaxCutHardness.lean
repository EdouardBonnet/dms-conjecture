import Lax762056.GraphProblems

/-!
---
title: NP-hardness of unweighted Max Cut
type: lemma
---
Deciding whether a finite simple unweighted graph has a cut of size at
least $k$ is NP-hard (Garey, Johnson, and Stockmeyer, 1976).
-/

namespace Lax762056.MaxCutHardness

open GraphProblems

axiom maxCut_hardness : NPHard MaxCut

end Lax762056.MaxCutHardness
