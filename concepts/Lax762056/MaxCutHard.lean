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

This is a prerequisite of Theorem 5, rather than an assumption in its
statement. Its proof is to use the pending Cook–Levin submission, followed
by the standard satisfiability-to-Max-Cut reductions. In particular, a
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
