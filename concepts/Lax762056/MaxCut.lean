import Lax762056.GraphEncoding

/-!
---
title: Maximum cuts
type: definition
---
For a graph $F$ on an ordered vertex set, each edge is represented once, by
its endpoints $u<v$. A cut is specified by a subset $S$ of vertices; its size
is the number of edges with exactly one endpoint in $S$. $\operatorname{MaxCut}(F)$
is the largest such size, with value zero for an edgeless graph.
-/

namespace Lax762056.MaxCut

noncomputable def edges {n : ℕ} (F : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

noncomputable def cutSize {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((edges F).filter fun e => (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)).card

noncomputable def maxCut {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ : Finset (Fin n)).powerset.sup (cutSize F)

end Lax762056.MaxCut
