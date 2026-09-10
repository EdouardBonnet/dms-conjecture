import Lax762056.MaxCut
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: Graph decision problems and NP-hardness
type: definition
---
Independent Set asks whether a graph has an independent set of size at least
$k$. Max Cut asks whether it has a cut with at least $k$ crossing edges.

A graph problem is NP-hard on a class $\mathcal C$ if every language in NP
has a polynomial-time many-one reduction to the problem whose output graph
always belongs to $\mathcal C$. Instances use the adjacency-matrix encoding.
-/

namespace Lax762056.GraphProblems

open GraphEncoding
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

abbrev GraphClass := ∀ {n : ℕ}, SimpleGraph (Fin n) → Prop
abbrev DecisionProblem := Instance → Prop

def IndependentSet (I : Instance) : Prop := I.threshold ≤ I.graph.indepNum

def MaxCut (I : Instance) : Prop := I.threshold ≤ Lax762056.MaxCut.maxCut I.graph

def NPHard (problem : DecisionProblem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
      ∀ x, x ∈ A ↔ problem (f x)

def NPHardOn (problem : DecisionProblem) (graphs : GraphClass) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encode f) ∧
      ∀ x, graphs (f x).graph ∧ (x ∈ A ↔ problem (f x))

end Lax762056.GraphProblems
