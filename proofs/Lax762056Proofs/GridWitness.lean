import Lax762056.CycleObstruction
import Mathlib.Tactic

namespace Lax762056Proofs.GridWitness

open Lax762056 AsteroidalCycles Grid

local instance : DecidableRel (squareGrid 5).Adj := by
  intro u v
  exact decidable_of_iff
    (((u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val) ∧ u.2 = v.2) ∨
     ((u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val) ∧ u.1 = v.1))
    (by simp only [squareGrid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj])

def base : Fin 3 → Fin 5 × Fin 5 := ![(0, 0), (0, 3), (3, 0)]

def cycle (i : Fin 3) : (squareGrid 5).Walk (base i) (base i) :=
  match i with
  | 0 => .cons (show (squareGrid 5).Adj (0, 0) (0, 1) by decide)
      (.cons (show (squareGrid 5).Adj (0, 1) (1, 1) by decide)
      (.cons (show (squareGrid 5).Adj (1, 1) (1, 0) by decide)
      (.cons (show (squareGrid 5).Adj (1, 0) (0, 0) by decide) .nil)))
  | 1 => .cons (show (squareGrid 5).Adj (0, 3) (0, 4) by decide)
      (.cons (show (squareGrid 5).Adj (0, 4) (1, 4) by decide)
      (.cons (show (squareGrid 5).Adj (1, 4) (1, 3) by decide)
      (.cons (show (squareGrid 5).Adj (1, 3) (0, 3) by decide) .nil)))
  | 2 => .cons (show (squareGrid 5).Adj (3, 0) (3, 1) by decide)
      (.cons (show (squareGrid 5).Adj (3, 1) (4, 1) by decide)
      (.cons (show (squareGrid 5).Adj (4, 1) (4, 0) by decide)
      (.cons (show (squareGrid 5).Adj (4, 0) (3, 0) by decide) .nil)))

def path01 : (squareGrid 5).Walk (0, 1) (0, 3) :=
  .cons (show (squareGrid 5).Adj (0, 1) (0, 2) by decide) (.cons (by decide) .nil)

def path02 : (squareGrid 5).Walk (1, 0) (3, 0) :=
  .cons (show (squareGrid 5).Adj (1, 0) (2, 0) by decide) (.cons (by decide) .nil)

def path12 : (squareGrid 5).Walk (1, 4) (4, 1) :=
  .cons (show (squareGrid 5).Adj (1, 4) (2, 4) by decide)
    (.cons (show (squareGrid 5).Adj (2, 4) (3, 4) by decide)
    (.cons (show (squareGrid 5).Adj (3, 4) (4, 4) by decide)
    (.cons (show (squareGrid 5).Adj (4, 4) (4, 3) by decide)
    (.cons (show (squareGrid 5).Adj (4, 3) (4, 2) by decide)
    (.cons (by decide) .nil)))))

theorem path01_isPath : path01.IsPath := by
  simp [SimpleGraph.Walk.isPath_def, path01]

theorem path02_isPath : path02.IsPath := by
  simp [SimpleGraph.Walk.isPath_def, path02]

theorem path12_isPath : path12.IsPath := by
  simp [SimpleGraph.Walk.isPath_def, path12]

theorem cycles : ∀ i, (cycle i).IsCycle := by
  intro i
  fin_cases i <;>
    simp [cycle, base, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons]

theorem separated : ∀ i j, i ≠ j →
    ∀ u ∈ (cycle i).support, ∀ v ∈ (cycle j).support,
      u ≠ v ∧ ¬ (squareGrid 5).Adj u v := by decide

theorem paths : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    ∃ u ∈ (cycle i).support, ∃ v ∈ (cycle j).support,
      ∃ p : (squareGrid 5).Path u v, ∀ x ∈ p.val.support, ∀ y ∈ (cycle k).support,
        x ≠ y ∧ ¬ (squareGrid 5).Adj x y := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  · exact ⟨(0, 1), by decide, (0, 3), by decide, ⟨path01, path01_isPath⟩, by decide⟩
  · exact ⟨(1, 0), by decide, (3, 0), by decide, ⟨path02, path02_isPath⟩, by decide⟩
  · exact ⟨(0, 3), by decide, (0, 1), by decide, ⟨path01.reverse, path01_isPath.reverse⟩, by decide⟩
  · exact ⟨(1, 4), by decide, (4, 1), by decide, ⟨path12, path12_isPath⟩, by decide⟩
  · exact ⟨(3, 0), by decide, (1, 0), by decide, ⟨path02.reverse, path02_isPath.reverse⟩, by decide⟩
  · exact ⟨(4, 1), by decide, (1, 4), by decide, ⟨path12.reverse, path12_isPath.reverse⟩, by decide⟩

/--
---
conclusion: Lax762056.CycleObstruction.grid_five_has_asteroidalCycles
---
Three corner squares form an asteroidal triple, joined pairwise by paths
along the boundary of the grid.
-/
theorem grid_five_has_asteroidalCycles : HasAsteroidalCycleTriple (squareGrid 5) :=
  ⟨base, cycle, cycles, fun {_ _} h => separated _ _ h, paths⟩

end Lax762056Proofs.GridWitness
