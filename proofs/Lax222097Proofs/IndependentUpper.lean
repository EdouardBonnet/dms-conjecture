import Lax222097Proofs.Counting
import Lax222097Proofs.ReductionBasics

namespace Lax222097Proofs.IndependentUpper

open Lax222097 ReductionBasics

noncomputable section

variable {n : ℕ} {F : SimpleGraph (Fin n)}

def rowVertices (I : Finset (Vtx F)) (r : Reduction.Row F) : Finset (Vtx F) := by
  classical
  exact I.filter fun x => row x = r

def rowColumns (I : Finset (Vtx F)) (r : Reduction.Row F) : Finset ℕ :=
  (rowVertices I r).image col

theorem mem_columns {I : Finset (Vtx F)} {r : Reduction.Row F} {j : ℕ} :
    j ∈ rowColumns I r ↔ ∃ x ∈ I, row x = r ∧ col x = j := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, hcol⟩ := Finset.mem_image.mp h
    have hx := Finset.mem_filter.mp hx
    exact ⟨x, hx.1, hx.2, hcol⟩
  · rintro ⟨x, hx, hr, hcol⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hr⟩, hcol⟩

theorem columns_card {I : Finset (Vtx F)}
    (hI : (Reduction.reductionGraph F).IsIndepSet I) (r : Reduction.Row F) :
    (rowColumns I r).card = (rowVertices I r).card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy hcol
  have hx := Finset.mem_filter.mp hx
  have hy := Finset.mem_filter.mp hy
  have hrow : row x = row y := hx.2.trans hy.2.symm
  have hside := independent_same_column hI hx.1 hy.1 hcol
  apply Subtype.ext
  exact Prod.ext hrow (Prod.ext (Fin.ext hcol) hside)

theorem row_bound {I : Finset (Vtx F)} (hI : (Reduction.reductionGraph F).IsIndepSet I)
    (e : Reduction.Edge F) (t : Bool) :
    (rowColumns I (e, t)).card ≤ span e + 1 ∧
    (span e < (rowColumns I (e, t)).card →
      2 * lo e ∈ rowColumns I (e, t) ∧ 2 * hi e ∈ rowColumns I (e, t)) := by
  have he := lo_lt_hi e
  have hbound : ∀ j ∈ rowColumns I (e, t), 2 * lo e ≤ j ∧ j ≤ 2 * lo e + 2 * span e := by
    intro j hj
    obtain ⟨x, hx, hr, rfl⟩ := mem_columns.mp hj
    have hb := bounds x
    simp only [hr] at hb
    dsimp only [span]
    omega
  have hsep : ∀ j ∈ rowColumns I (e, t), ∀ k ∈ rowColumns I (e, t), j + 1 ≠ k := by
    intro j hj k hk
    obtain ⟨x, hx, hrx, rfl⟩ := mem_columns.mp hj
    obtain ⟨y, hy, hry, rfl⟩ := mem_columns.mp hk
    exact independent_separated hI hx hy (hrx.trans hry.symm)
  have h := Counting.row_bound (rowColumns I (e, t)) (2 * lo e) (span e) hbound hsep
  have heq : 2 * lo e + 2 * span e = 2 * hi e := by dsimp only [span]; omega
  simpa only [heq] using h

def cutSide (I : Finset (Vtx F)) (v : Fin n) : Bool := by
  classical
  exact decide (∃ x ∈ I, col x = 2 * v.val ∧ side x = true)

theorem cutSide_eq {I : Finset (Vtx F)} (hI : (Reduction.reductionGraph F).IsIndepSet I)
    {x : Vtx F} (hx : x ∈ I) (v : Fin n) (hv : col x = 2 * v.val) :
    cutSide I v = side x := by
  classical
  unfold cutSide
  cases hs : side x
  · apply decide_eq_false_iff_not.mpr
    rintro ⟨y, hy, hcol, hside⟩
    have := independent_same_column hI hx hy (hv.trans hcol.symm)
    simp_all
  · simp only [decide_eq_true_eq]
    exact ⟨x, hx, hv, hs⟩

theorem full_row_endpoints {I : Finset (Vtx F)}
    (hI : (Reduction.reductionGraph F).IsIndepSet I) (e : Reduction.Edge F) (t : Bool)
    (hlarge : span e < (rowColumns I (e, t)).card) :
    cutSide I e.val.1 = t ∧ cutSide I e.val.2 = !t := by
  obtain ⟨ha, hb⟩ := (row_bound hI e t).2 hlarge
  obtain ⟨x, hx, hrx, hcx⟩ := mem_columns.mp ha
  obtain ⟨y, hy, hry, hcy⟩ := mem_columns.mp hb
  have hsx := side_at_lo x (by simpa only [hrx] using hcx)
  have hsy := side_at_hi y (by simpa only [hry] using hcy)
  simp only [hrx, hry] at hsx hsy
  exact ⟨(cutSide_eq hI hx e.val.1 hcx).trans hsx,
    (cutSide_eq hI hy e.val.2 hcy).trans hsy⟩

theorem edge_bound {I : Finset (Vtx F)} (hI : (Reduction.reductionGraph F).IsIndepSet I)
    (e : Reduction.Edge F) :
    (rowColumns I (e, false)).card + (rowColumns I (e, true)).card ≤
      2 * span e + if cutSide I e.val.1 ≠ cutSide I e.val.2 then 1 else 0 := by
  have h0 := (row_bound hI e false).1
  have h1 := (row_bound hI e true).1
  have hn : ¬ (span e < (rowColumns I (e, false)).card ∧
      span e < (rowColumns I (e, true)).card) := by
    rintro ⟨ha, hb⟩
    have hfalse := (full_row_endpoints hI e false ha).1
    have htrue := (full_row_endpoints hI e true hb).1
    simp_all
  split_ifs with hcut
  · omega
  · have hsame : cutSide I e.val.1 = cutSide I e.val.2 := not_ne_iff.mp hcut
    have hb (t : Bool) : (rowColumns I (e, t)).card ≤ span e := by
      by_contra h
      have he := full_row_endpoints hI e t (by omega)
      cases t <;> simp_all
    have := hb false
    have := hb true
    omega

def cutSet (I : Finset (Vtx F)) : Finset (Fin n) :=
  Finset.univ.filter fun v => cutSide I v = true

theorem cutSize_eq_sum (I : Finset (Vtx F)) :
    MaxCut.cutSize F (cutSet I) =
      ∑ e : Reduction.Edge F, if cutSide I e.val.1 ≠ cutSide I e.val.2 then 1 else 0 := by
  classical
  rw [sum_edges F (fun e => if cutSide I e.1 ≠ cutSide I e.2 then 1 else 0)]
  unfold MaxCut.cutSize
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  cases ha : cutSide I e.1 <;> cases hb : cutSide I e.2 <;>
    simp [cutSet, ha, hb]

theorem card_bound {I : Finset (Vtx F)} (hI : (Reduction.reductionGraph F).IsIndepSet I) :
    I.card ≤ MaxCut.maxCut F + Reduction.offset F := by
  classical
  have hsum : I.card = ∑ r : Reduction.Row F, (rowVertices I r).card := by
    exact Finset.card_eq_sum_card_fiberwise (f := row)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hc : MaxCut.cutSize F (cutSet I) ≤ MaxCut.maxCut F :=
    Finset.le_sup (Finset.mem_powerset.mpr (Finset.subset_univ _))
  calc
    I.card = ∑ e : Reduction.Edge F,
        ((rowColumns I (e, false)).card + (rowColumns I (e, true)).card) := by
      rw [hsum, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e he
      rw [Fintype.sum_bool, columns_card hI, columns_card hI, Nat.add_comm]
    _ ≤ ∑ e : Reduction.Edge F,
        (2 * span e + if cutSide I e.val.1 ≠ cutSide I e.val.2 then 1 else 0) :=
      Finset.sum_le_sum (fun e _ => edge_bound hI e)
    _ = Reduction.offset F + MaxCut.cutSize F (cutSet I) := by
      rw [Finset.sum_add_distrib, sum_span, cutSize_eq_sum]
    _ ≤ MaxCut.maxCut F + Reduction.offset F := by omega

theorem independence_upper :
    (Reduction.reductionGraph F).indepNum ≤ MaxCut.maxCut F + Reduction.offset F := by
  obtain ⟨I, hI⟩ := (Reduction.reductionGraph F).exists_isNIndepSet_indepNum
  have := card_bound hI.isIndepSet
  simpa only [hI.card_eq] using this

end

end Lax222097Proofs.IndependentUpper
