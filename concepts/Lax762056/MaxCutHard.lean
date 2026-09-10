import Lax762056.MaxCut
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: NP-hardness of unweighted Max Cut
type: lemma
---
Every language in NP reduces in polynomial time to the decision version of
Max Cut on finite simple unweighted graphs. For every binary input the
reduction outputs a well-formed graph and threshold, with cut size at least
the threshold exactly on yes-inputs.

The classical result is due to Garey, Johnson, and Stockmeyer (1976).
This is a prerequisite of Theorem 5. Its proof uses the Cook–Levin circuit
compiler from lax-429075, followed by the satisfiability-to-Max-Cut
reductions, each implemented by a polynomial-time machine. In particular, a
weighted or multigraph Max Cut hardness result alone does not discharge
this obligation.
-/

namespace Lax762056.MaxCutHard

open GraphEncoding MaxCut
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

axiom np_hard (A : Language) (hA : A ∈ NP) :
  ∃ f : Word → Instance,
    Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
    ∀ x, x ∈ A ↔ (f x).threshold ≤ maxCut (f x).graph

end Lax762056.MaxCutHard
