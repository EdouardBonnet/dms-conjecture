import Lax762056Proofs.ReductionBasics
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Lax762056Proofs.ColumnSets

open Lax762056

variable {R : Type*} {c : ℕ}

abbrev V := ColumnGraph.Vertex R c
abbrev G := ColumnGraph.graph R c
abbrev column (x : V (R := R) (c := c)) : ℕ := x.2.1.val

def Thin (U : Set (V (R := R) (c := c))) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, column x = column y → x.2.2 = y.2.2

theorem thin_mono {U S : Set (V (R := R) (c := c))} (hU : Thin U) (hS : S ⊆ U) : Thin S :=
  fun x hx y hy h => hU x (hS hx) y (hS hy) h

theorem step_bound {x y : V (R := R) (c := c)} (h : G.Adj x y) :
    column y ≤ column x + 1 := by
  dsimp only [column]
  rcases (ReductionBasics.column_adj x y).mp h with ⟨h, _⟩ | ⟨_, h | h⟩
  · have := congrArg Fin.val h
    omega
  · omega
  · omega

theorem thin_adj {U : Set (V (R := R) (c := c))} (hU : Thin U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) (hadj : G.Adj x y) : x.1 = y.1 := by
  rcases (ReductionBasics.column_adj x y).mp hadj with ⟨hc, hs⟩ | ⟨hr, _⟩
  · exact (hs (hU x hx y hy (congrArg Fin.val hc))).elim
  · exact hr

theorem connected_row {S : Set (V (R := R) (c := c))}
    (hS : (G.induce S).Connected) (hthin : Thin S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : x.1 = y.1 := by
  obtain ⟨p⟩ := hS ⟨x, hx⟩ ⟨y, hy⟩
  have aux : ∀ {a b : S}, (G.induce S).Walk a b → a.val.1 = b.val.1 := by
    intro a b w
    induction w with
    | nil => rfl
    | @cons a b d hab p ih =>
      exact (thin_adj hthin a.property b.property hab).trans ih
  exact aux p

theorem walk_hits {S : Set (V (R := R) (c := c))} {x y : S}
    (p : (G.induce S).Walk x y) (k : ℕ)
    (hx : column x.val ≤ k) (hy : k ≤ column y.val) :
    ∃ z : S, column z.val = k := by
  induction p with
  | @nil a => exact ⟨a, by omega⟩
  | @cons a b d hab p ih =>
    by_cases h : column a.val = k
    · exact ⟨a, h⟩
    · have hstep : column b.val ≤ column a.val + 1 :=
        step_bound (show G.Adj a.val b.val from hab)
      exact ih (by omega) hy

theorem connected_hits {S : Set (V (R := R) (c := c))}
    (hS : (G.induce S).Connected) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (k : ℕ) (hxk : column x ≤ k) (hyk : k ≤ column y) :
    ∃ z ∈ S, column z = k := by
  obtain ⟨p⟩ := hS ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨z, hz⟩ := walk_hits p k hxk hyk
  exact ⟨z.val, z.property, hz⟩

noncomputable def columns (S : Set (V (R := R) (c := c))) : Finset (Fin c) := by
  classical
  exact Finset.univ.filter fun j => ∃ x ∈ S, x.2.1 = j

noncomputable def maxColumn (S : Set (V (R := R) (c := c))) : ℕ :=
  (columns S).sup Fin.val

theorem le_maxColumn {S : Set (V (R := R) (c := c))} {x : V} (hx : x ∈ S) :
    column x ≤ maxColumn S := by
  classical
  exact Finset.le_sup (s := columns S) (b := x.2.1)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx, rfl⟩⟩)

theorem maxColumn_mem {S : Set (V (R := R) (c := c))} (hS : S.Nonempty) :
    ∃ x ∈ S, column x = maxColumn S := by
  classical
  have hne : (columns S).Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨x.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx, rfl⟩⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (columns S) hne Fin.val
  obtain ⟨x, hx, hxj⟩ := (Finset.mem_filter.mp hj).2
  exact ⟨x, hx, (congrArg Fin.val hxj).trans hmax.symm⟩

theorem equal_of_row_column {U : Set (V (R := R) (c := c))} (hU : Thin U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) (hr : x.1 = y.1) (hc : column x = column y) :
    x = y :=
  Prod.ext hr (Prod.ext (Fin.ext hc) (hU x hx y hy hc))

/-- Two disjoint connected sets in a thin set can touch only at their
interval endpoints. The set with the larger right endpoint starts one
column beyond the smaller set's right endpoint. -/
theorem touch_above {U S T : Set (V (R := R) (c := c))}
    (hU : Thin U) (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hS : (G.induce S).Connected) (hT : (G.induce T).Connected)
    (hdis : Disjoint S T) (hmax : maxColumn S ≤ maxColumn T)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T) (hadj : G.Adj x y) :
    column y = maxColumn S + 1 := by
  have hrow := thin_adj hU (hSU hx) (hTU hy) hadj
  have hxs := le_maxColumn hx
  have hys := le_maxColumn hy
  have hstep := step_bound hadj
  have hthinS := thin_mono hU hSU
  have hthinT := thin_mono hU hTU
  obtain ⟨a, ha, hac⟩ := maxColumn_mem (show S.Nonempty from ⟨x, hx⟩)
  obtain ⟨b, hb, hbc⟩ := maxColumn_mem (show T.Nonempty from ⟨y, hy⟩)
  have hygt : maxColumn S < column y := by
    by_contra hn
    have hyle : column y ≤ maxColumn S := by omega
    by_cases hxy : column x ≤ column y
    · obtain ⟨z, hz, hzc⟩ := connected_hits hS hx ha (column y) hxy (by omega)
      have hzr := (connected_row hS hthinS hz hx).trans hrow
      have hzy := equal_of_row_column hU (hSU hz) (hTU hy) hzr hzc
      exact Set.disjoint_left.mp hdis (hzy ▸ hz) hy
    · obtain ⟨z, hz, hzc⟩ := connected_hits hT hy hb (column x) (by omega) (by omega)
      have hzr := (connected_row hT hthinT hz hy).trans hrow.symm
      have hzx := equal_of_row_column hU (hTU hz) (hSU hx) hzr hzc
      exact Set.disjoint_left.mp hdis hx (hzx ▸ hz)
  omega

end Lax762056Proofs.ColumnSets
