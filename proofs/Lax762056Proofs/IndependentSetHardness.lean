import Lax762056.IndependentSetHardness
import Lax762056.MaxCutHardness
import Lax762056.ReductionTime
import Lax762056Proofs.GridExclusion
import Lax762056Proofs.IndependenceIdentity
import Lax762056Proofs.IsoTransport
import Lax762056Proofs.PolynomialComposition
import Lax762056Proofs.ReductionTime
import Lax762056Proofs.MaxCutHardness

namespace Lax762056Proofs

open Lax762056 GraphProblems Grid

/--
---
conclusion: Lax762056.IndependentSetHardness.independentSet_inducedGrid_hardness
---
Compose the reduction from Max Cut with the graph construction. Exclusion
of the induced grid minor gives the target class. The independence-number
identity gives equivalence after shifting the threshold.
-/
theorem independentSet_inducedGrid_hardness :
    NPHardOn IndependentSet (ExcludesInducedGrid 5) := by
  intro A hA
  obtain ⟨f, ⟨hf⟩, hcorrect⟩ := maxCut_hardness A hA
  obtain ⟨g, ⟨hg⟩, hgraph⟩ := reduction_polynomial_time
  refine ⟨g ∘ f, PolynomialComposition.comp hf hg, ?_⟩
  intro x
  obtain ⟨⟨e⟩, ht⟩ := hgraph (f x)
  refine ⟨IsoTransport.excludes_inducedGrid e (reduction_excludes_inducedGrid _), ?_⟩
  change x ∈ A ↔ (g (f x)).threshold ≤ (g (f x)).graph.indepNum
  rw [ht, IsoTransport.indepNum_eq e, independence_eq_maxCut_offset, hcorrect x]
  exact Nat.add_le_add_iff_right.symm

end Lax762056Proofs
