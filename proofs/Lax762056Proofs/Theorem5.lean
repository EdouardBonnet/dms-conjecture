import Lax762056.Theorem5
import Lax762056.MaxCutHard
import Lax762056.ReductionTime
import Lax762056Proofs.GridExclusion
import Lax762056Proofs.IndependenceIdentity
import Lax762056Proofs.IsoTransport
import Lax762056Proofs.PolynomialComposition
import Lax762056Proofs.ReductionTime
import Lax762056Proofs.MaxCutHard

namespace Lax762056Proofs

open Lax762056 GraphEncoding Lax434930.PolynomialTime
  Lax434930.NondeterministicPolynomialTime

/--
---
conclusion: Lax762056.Theorem5.np_hard
---
Compose the proved Max Cut hardness reduction with the encoded construction,
then apply the induced-minor exclusion and independence-number identity.
The proof uses the published Cook–Levin circuit compiler and Tseitin
correctness; every graph and machine lemma specific to this submission is proved.
-/
theorem theorem5 (A : Language) (hA : A ∈ NP) :
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
      ∀ x, Grid.ExcludesGrid (f x).graph ∧
        (x ∈ A ↔ (f x).threshold ≤ (f x).graph.indepNum) := by
  obtain ⟨f, ⟨hf⟩, hcorrect⟩ := maxCut_np_hard A hA
  obtain ⟨g, ⟨hg⟩, hgraph⟩ := reduction_polynomial_time
  refine ⟨g ∘ f, PolynomialComposition.comp hf hg, ?_⟩
  intro x
  obtain ⟨⟨e⟩, ht⟩ := hgraph (f x)
  refine ⟨IsoTransport.excludes_grid e (reduction_excludes_grid _), ?_⟩
  change x ∈ A ↔ (g (f x)).threshold ≤ (g (f x)).graph.indepNum
  rw [ht, IsoTransport.indepNum_eq e, independence_identity, hcorrect x]
  exact Nat.add_le_add_iff_right.symm

end Lax762056Proofs
