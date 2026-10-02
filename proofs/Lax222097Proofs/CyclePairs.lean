import Lax222097Proofs.ColumnSets
import Lax222097Proofs.InducedModels

namespace Lax222097Proofs.CyclePairs

open Lax222097 ColumnSets InducedModels

variable {R W : Type*} {c : ℕ} {H : SimpleGraph W}

/-- A cycle represented by connected branch sets cannot fit into a set
that chooses at most one side of each column. -/
theorem cycle_not_thin (M : InducedMinors.Model H (ColumnGraph.columnGraph R c))
    {v : W} (p : H.Walk v v) (hp : p.IsCycle) :
    ¬ Thin (union M {w | w ∈ p.support}) := by
  classical
  intro hthin
  obtain ⟨u, hu, hmin⟩ := p.support.toFinset.exists_min_image
    (fun w => maxColumn (M.branch w))
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have hu' : u ∈ p.support := List.mem_toFinset.mp hu
  let q := p.rotate u hu'
  have hq : q.IsCycle := hp.rotate hu'
  have hmem : ∀ w ∈ q.support, w ∈ p.support := by
    intro w hw
    exact (p.mem_support_rotate_iff u hu').mp hw
  have hv : q.snd ∈ p.support := hmem _ (q.getVert_mem_support 1)
  have hw : q.penultimate ∈ p.support := hmem _ (q.getVert_mem_support (q.length - 1))
  have hadjv : H.Adj u q.snd := q.adj_snd hq.not_nil
  have hadjw : H.Adj u q.penultimate := (q.adj_penultimate hq.not_nil).symm
  have hBu : M.branch u ⊆ union M {w | w ∈ p.support} := branch_subset M hu'
  have hBv : M.branch q.snd ⊆ union M {w | w ∈ p.support} := branch_subset M hv
  have hBw : M.branch q.penultimate ⊆ union M {w | w ∈ p.support} := branch_subset M hw
  obtain ⟨a, ha, b, hb, hab⟩ := (M.adjacent u q.snd hadjv.ne).mp hadjv
  obtain ⟨a', ha', d, hd, had⟩ := (M.adjacent u q.penultimate hadjw.ne).mp hadjw
  have hbc := touch_above hthin hBu hBv (M.connected u) (M.connected q.snd)
    (M.disjoint u q.snd hadjv.ne) (hmin _ (List.mem_toFinset.mpr hv)) ha hb hab
  have hdc := touch_above hthin hBu hBw (M.connected u) (M.connected q.penultimate)
    (M.disjoint u q.penultimate hadjw.ne) (hmin _ (List.mem_toFinset.mpr hw)) ha' hd had
  have hba := (thin_adj hthin (hBu ha) (hBv hb) hab).symm
  have haa' := connected_row (M.connected u) (thin_mono hthin hBu) ha ha'
  have ha'd := thin_adj hthin (hBu ha') (hBw hd) had
  have hbd := equal_of_row_column hthin (hBv hb) (hBw hd)
    (hba.trans (haa'.trans ha'd)) (hbc.trans hdc.symm)
  exact Set.disjoint_left.mp (M.disjoint q.snd q.penultimate hq.snd_ne_penultimate)
    (hbd ▸ hb) hd

theorem cycle_pair (M : InducedMinors.Model H (ColumnGraph.columnGraph R c))
    {v : W} (p : H.Walk v v) (hp : p.IsCycle) :
    ∃ x ∈ union M {w | w ∈ p.support}, ∃ y ∈ union M {w | w ∈ p.support},
      column x = column y ∧ x.2.2 ≠ y.2.2 := by
  classical
  by_contra h
  apply cycle_not_thin M p hp
  intro x hx y hy hcol
  by_contra hside
  exact h ⟨x, hx, y, hy, hcol, hside⟩

end Lax222097Proofs.CyclePairs
