import Lax762056.CycleObstruction
import Mathlib.Tactic

namespace Lax762056Proofs.GridWitness

open Lax762056

local instance : DecidableRel Grid.grid.Adj := by
  intro u v
  exact decidable_of_iff
    (((u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val) ∧ u.2 = v.2) ∨
     ((u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val) ∧ u.1 = v.1))
    (by simp only [Grid.grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj])

def base : Fin 3 → Fin 5 × Fin 5 := ![(0, 0), (0, 3), (3, 0)]

def cycle (i : Fin 3) : Grid.grid.Walk (base i) (base i) :=
  match i with
  | 0 => .cons (show Grid.grid.Adj (0, 0) (0, 1) by decide)
      (.cons (show Grid.grid.Adj (0, 1) (1, 1) by decide)
      (.cons (show Grid.grid.Adj (1, 1) (1, 0) by decide)
      (.cons (show Grid.grid.Adj (1, 0) (0, 0) by decide) .nil)))
  | 1 => .cons (show Grid.grid.Adj (0, 3) (0, 4) by decide)
      (.cons (show Grid.grid.Adj (0, 4) (1, 4) by decide)
      (.cons (show Grid.grid.Adj (1, 4) (1, 3) by decide)
      (.cons (show Grid.grid.Adj (1, 3) (0, 3) by decide) .nil)))
  | 2 => .cons (show Grid.grid.Adj (3, 0) (3, 1) by decide)
      (.cons (show Grid.grid.Adj (3, 1) (4, 1) by decide)
      (.cons (show Grid.grid.Adj (4, 1) (4, 0) by decide)
      (.cons (show Grid.grid.Adj (4, 0) (3, 0) by decide) .nil)))

def path01 : Grid.grid.Walk (0, 1) (0, 3) :=
  .cons (show Grid.grid.Adj (0, 1) (0, 2) by decide) (.cons (by decide) .nil)

def path02 : Grid.grid.Walk (1, 0) (3, 0) :=
  .cons (show Grid.grid.Adj (1, 0) (2, 0) by decide) (.cons (by decide) .nil)

def path12 : Grid.grid.Walk (1, 4) (4, 1) :=
  .cons (show Grid.grid.Adj (1, 4) (2, 4) by decide)
    (.cons (show Grid.grid.Adj (2, 4) (3, 4) by decide)
    (.cons (show Grid.grid.Adj (3, 4) (4, 4) by decide)
    (.cons (show Grid.grid.Adj (4, 4) (4, 3) by decide)
    (.cons (show Grid.grid.Adj (4, 3) (4, 2) by decide)
    (.cons (by decide) .nil)))))

theorem cycles : ∀ i, (cycle i).IsCycle := by
  intro i
  fin_cases i <;>
    simp [cycle, base, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons]

theorem separated : ∀ i j, i ≠ j →
    ∀ u ∈ (cycle i).support, ∀ v ∈ (cycle j).support,
      u ≠ v ∧ ¬ Grid.grid.Adj u v := by decide

theorem paths : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    ∃ u ∈ (cycle i).support, ∃ v ∈ (cycle j).support,
      ∃ p : Grid.grid.Walk u v, ∀ x ∈ p.support, ∀ y ∈ (cycle k).support,
        x ≠ y ∧ ¬ Grid.grid.Adj x y := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  · exact ⟨(0, 1), by decide, (0, 3), by decide, path01, by decide⟩
  · exact ⟨(1, 0), by decide, (3, 0), by decide, path02, by decide⟩
  · exact ⟨(0, 3), by decide, (0, 1), by decide, path01.reverse, by decide⟩
  · exact ⟨(1, 4), by decide, (4, 1), by decide, path12, by decide⟩
  · exact ⟨(3, 0), by decide, (1, 0), by decide, path02.reverse, by decide⟩
  · exact ⟨(4, 1), by decide, (1, 4), by decide, path12.reverse, by decide⟩

/--
---
conclusion: Lax762056.CycleObstruction.grid_has_triple
---
The three corner squares and boundary paths are explicit finite walks.
Their cycle, separation, and avoidance conditions are checked by reduction
in the Lean kernel.
-/
theorem grid_has_triple : AsteroidalCycles.HasTriple Grid.grid :=
  ⟨base, cycle, cycles, separated, paths⟩

end Lax762056Proofs.GridWitness
