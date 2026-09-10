import Lax762056.MaxCutHard
import Lax762056Proofs.CookBridge

namespace Lax762056Proofs

open Lax762056 GraphEncoding MaxCut
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/--
---
conclusion: Lax762056.MaxCutHard.np_hard
---
Compose the Cook–Levin circuit compiler with the finite machine constructing
the unweighted simple Max Cut gadgets. Unit and binary clauses are padded by
literal repetition; all edge occurrences receive distinct subdivision vertices.
-/
theorem maxCut_np_hard (A : Language) (hA : A ∈ NP) :
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
      ∀ x, x ∈ A ↔ (f x).threshold ≤ maxCut (f x).graph := by
  obtain ⟨V, hV, p, hA⟩ := hA
  obtain ⟨f, hf, hc⟩ := CookBridge.compile V hV p
  exact ⟨f, hf, fun x => (hA x).trans (hc x)⟩

end Lax762056Proofs
