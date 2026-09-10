import Lax762056Proofs.ReductionBasics

namespace Lax762056Proofs.IndependentLower

open Lax762056 ReductionBasics

noncomputable section

variable {n : ℕ} {F : SimpleGraph (Fin n)}

def tag (ρ : Fin n → Bool) (e : Reduction.Edge F) (q : ℕ) : Bool :=
  if q = 2 * span e then !(ρ e.val.2)
  else if q % 2 = 0 then ρ e.val.1 else !(ρ e.val.1)

def columnSide (ρ : Fin n → Bool) (j : Fin (2 * n - 1)) : Bool :=
  if j.val % 2 = 0 then ρ ⟨j.val / 2, by have := j.isLt; omega⟩ else false

def vertex (ρ : Fin n → Bool) (e : Reduction.Edge F) (q : ℕ)
    (hq : q ≤ 2 * span e) : Vtx F := by
  let j : Fin (2 * n - 1) := ⟨2 * lo e + q, by
    have hlo := lo_lt_hi e
    have hv := e.val.2.isLt
    dsimp only [span, lo, hi] at *
    omega⟩
  refine ⟨((e, tag ρ e q), j, columnSide ρ j), ?_⟩
  change (j.val = 2 * lo e ∧ columnSide ρ j = tag ρ e q) ∨
    (2 * lo e < j.val ∧ j.val < 2 * hi e) ∨
    (j.val = 2 * hi e ∧ columnSide ρ j = !(tag ρ e q))
  have hlo := lo_lt_hi e
  have hd : 0 < span e := by dsimp only [span]; omega
  have hspan : lo e + span e = hi e := by dsimp only [span]; omega
  by_cases hzero : q = 0
  · subst q
    apply Or.inl
    constructor
    · rfl
    · have hj : (⟨j.val / 2, by have := j.isLt; omega⟩ : Fin n) = e.val.1 := by
        apply Fin.ext
        dsimp only [j, lo]
        omega
      have hjpar : j.val % 2 = 0 := by dsimp only [j]; omega
      simp only [columnSide, hjpar, if_pos, hj, tag]
      rw [if_neg (by omega)]
  · by_cases hlast : q = 2 * span e
    · apply Or.inr ∘ Or.inr
      have hjval : j.val = 2 * hi e := by dsimp only [j, span] at *; omega
      refine ⟨hjval, ?_⟩
      simp [columnSide, hjval, tag, hlast]
    · apply Or.inr ∘ Or.inl
      change 2 * lo e < 2 * lo e + q ∧ 2 * lo e + q < 2 * hi e
      omega

theorem vertex_col (ρ : Fin n → Bool) (e : Reduction.Edge F) (q : ℕ) (hq) :
    col (vertex ρ e q hq) = 2 * lo e + q := rfl

theorem vertex_row (ρ : Fin n → Bool) (e : Reduction.Edge F) (q : ℕ) (hq) :
    row (vertex ρ e q hq) = (e, tag ρ e q) := rfl

theorem vertex_side (ρ : Fin n → Bool) (e : Reduction.Edge F) (q : ℕ) (hq) :
    side (vertex ρ e q hq) = columnSide ρ (vertex ρ e q hq).val.2.1 := rfl

def positions (ρ : Fin n → Bool) (e : Reduction.Edge F) : Finset ℕ :=
  if ρ e.val.1 ≠ ρ e.val.2 then Finset.range (2 * span e + 1)
  else (Finset.range (2 * span e + 1)).erase (2 * span e - 1)

theorem position_spec {ρ : Fin n → Bool} {e : Reduction.Edge F} {q : ℕ}
    (hq : q ∈ positions ρ e) :
    q ≤ 2 * span e ∧ (q = 2 * span e - 1 → ρ e.val.1 ≠ ρ e.val.2) := by
  unfold positions at hq
  split_ifs at hq with hcut
  · exact ⟨by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hq, fun _ => hcut⟩
  · obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hq
    exact ⟨by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hm,
      fun h => (hne h).elim⟩

theorem positions_card (ρ : Fin n → Bool) (e : Reduction.Edge F) :
    (positions ρ e).card = 2 * span e + if ρ e.val.1 ≠ ρ e.val.2 then 1 else 0 := by
  have hlo := lo_lt_hi e
  have hd : 0 < span e := by dsimp only [span]; omega
  unfold positions
  split_ifs with h
  · exact Finset.card_range _
  · rw [Finset.card_erase_of_mem (by simp only [Finset.mem_range]; omega), Finset.card_range]
    omega

theorem tag_step (ρ : Fin n → Bool) (e : Reduction.Edge F) (q r : ℕ)
    (hq : q ∈ positions ρ e) (hr : r ∈ positions ρ e) (hstep : q + 1 = r) :
    tag ρ e q ≠ tag ρ e r := by
  have hqs := position_spec hq
  have hrs := position_spec hr
  have hqne : q ≠ 2 * span e := by omega
  by_cases hlast : r = 2 * span e
  · have hodd : q % 2 ≠ 0 := by omega
    have hcut := hqs.2 (by omega)
    simp only [tag, hqne, if_false, hodd, hlast, if_true]
    cases ha : ρ e.val.1 <;> cases hb : ρ e.val.2 <;> simp_all
  · have hrne : r ≠ 2 * span e := hlast
    by_cases hpar : q % 2 = 0
    · have hrpar : r % 2 ≠ 0 := by omega
      simp only [tag, hqne, hrne, if_false, hpar, if_true, hrpar]
      cases ρ e.val.1 <;> decide
    · have hrpar : r % 2 = 0 := by omega
      simp only [tag, hqne, hrne, if_false, hpar, hrpar, if_true]
      cases ρ e.val.1 <;> decide

def selected (ρ : Fin n → Bool) : Finset (Σ _ : Reduction.Edge F, ℕ) :=
  Finset.univ.sigma (positions ρ)

theorem selected_mem {ρ : Fin n → Bool} {p : Σ _ : Reduction.Edge F, ℕ}
    (hp : p ∈ selected ρ) : p.2 ∈ positions ρ p.1 :=
  (Finset.mem_sigma.mp hp).2

def chosenVertex (ρ : Fin n → Bool) (p : ↥(selected (F := F) ρ)) : Vtx F :=
  vertex ρ p.val.1 p.val.2 (position_spec (selected_mem p.property)).1

def independentSet (ρ : Fin n → Bool) : Finset (Vtx F) := by
  classical
  exact (selected ρ).attach.image (chosenVertex ρ)

theorem chosenVertex_injective (ρ : Fin n → Bool) : Function.Injective (chosenVertex (F := F) ρ) := by
  intro p q hpq
  have he : p.val.1 = q.val.1 := congrArg (fun x => (row x).1) hpq
  have hc : 2 * lo p.val.1 + p.val.2 = 2 * lo q.val.1 + q.val.2 :=
    congrArg col hpq
  have hq : p.val.2 = q.val.2 := by rw [he] at hc; omega
  apply Subtype.ext
  exact Sigma.ext he (heq_of_eq hq)

theorem chosen_nonadjacent (ρ : Fin n → Bool) (p q : ↥(selected (F := F) ρ)) :
    ¬ (Reduction.graph F).Adj (chosenVertex ρ p) (chosenVertex ρ q) := by
  intro hadj
  rcases (adj _ _).mp hadj with ⟨hc, hs⟩ | ⟨hr, hc | hc⟩
  · apply hs
    change columnSide ρ _ = columnSide ρ _
    congr 1
    exact Fin.ext hc
  · have he : p.val.1 = q.val.1 := congrArg Prod.fst hr
    have ht : tag ρ p.val.1 p.val.2 = tag ρ q.val.1 q.val.2 := congrArg Prod.snd hr
    have hps := selected_mem p.property
    have hqs := selected_mem q.property
    change (2 * lo p.val.1 + p.val.2) + 1 = 2 * lo q.val.1 + q.val.2 at hc
    rw [he] at hc ht hps
    exact tag_step ρ q.val.1 p.val.2 q.val.2 hps hqs (by omega) ht
  · have he : p.val.1 = q.val.1 := congrArg Prod.fst hr
    have ht : tag ρ p.val.1 p.val.2 = tag ρ q.val.1 q.val.2 := congrArg Prod.snd hr
    have hps := selected_mem p.property
    have hqs := selected_mem q.property
    change (2 * lo q.val.1 + q.val.2) + 1 = 2 * lo p.val.1 + p.val.2 at hc
    rw [he] at hc ht hps
    exact tag_step ρ q.val.1 q.val.2 p.val.2 hqs hps (by omega) ht.symm

theorem is_independent (ρ : Fin n → Bool) :
    (Reduction.graph F).IsIndepSet (independentSet (F := F) ρ) := by
  classical
  intro x hx y hy hxy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  exact chosen_nonadjacent ρ p q

theorem card_independentSet (ρ : Fin n → Bool) :
    (independentSet (F := F) ρ).card =
      ∑ e : Reduction.Edge F, (2 * span e + if ρ e.val.1 ≠ ρ e.val.2 then 1 else 0) := by
  classical
  rw [independentSet, Finset.card_image_of_injective _ (chosenVertex_injective ρ),
    Finset.card_attach, selected, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun e _ => positions_card ρ e)

theorem lower_for_cut (S : Finset (Fin n)) :
    MaxCut.cutSize F S + Reduction.offset F ≤ (Reduction.graph F).indepNum := by
  classical
  let ρ : Fin n → Bool := fun v => decide (v ∈ S)
  have hcount : (∑ e : Reduction.Edge F, if ρ e.val.1 ≠ ρ e.val.2 then 1 else 0) =
      MaxCut.cutSize F S := by
    rw [sum_edges F (fun e => if ρ e.1 ≠ ρ e.2 then 1 else 0)]
    unfold MaxCut.cutSize
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases ha : e.1 ∈ S <;> by_cases hb : e.2 ∈ S <;> simp [ρ, ha, hb]
  have hcard : (independentSet (F := F) ρ).card = MaxCut.cutSize F S + Reduction.offset F := by
    rw [card_independentSet, Finset.sum_add_distrib, sum_span, hcount, Nat.add_comm]
  rw [← hcard]
  exact (is_independent ρ).card_le_indepNum

theorem independence_lower :
    MaxCut.maxCut F + Reduction.offset F ≤ (Reduction.graph F).indepNum := by
  classical
  obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin n)).powerset
    (by simp only [Finset.powerset_nonempty]) (MaxCut.cutSize F)
  have h := lower_for_cut (F := F) S
  change MaxCut.maxCut F = MaxCut.cutSize F S at hmax
  simpa only [hmax] using h

end

end Lax762056Proofs.IndependentLower
