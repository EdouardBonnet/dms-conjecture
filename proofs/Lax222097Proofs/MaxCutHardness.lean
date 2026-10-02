import Lax222097.MaxCutHardness
import Lax222097Proofs.CookBridge

namespace Lax222097Proofs

open Lax222097 GraphProblems
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/--
---
conclusion: Lax222097.MaxCutHardness.maxCut_hardness
---
Reduce satisfiability to not-all-equal clauses, then to Max Cut. Complementary
literals are joined by an edge, and each clause contributes a triangle.
Replacing each edge occurrence by a three-edge path yields a simple
unweighted graph.
-/
theorem maxCut_hardness : NPHard MaxCut := by
  intro A hA
  obtain ⟨V, hV, p, hA⟩ := hA
  obtain ⟨f, hf, hc⟩ := CookBridge.compile V hV p
  exact ⟨f, hf, fun x => (hA x).trans (hc x)⟩

end Lax222097Proofs
