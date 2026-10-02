import Lax222097.MaxCut
import Mathlib.Tactic

namespace Lax222097Proofs.CutScores

open Lax222097

def apart (a b : Bool) : ℕ := if a = b then 0 else 1

theorem apart_symm (a b : Bool) : apart a b = apart b a := by
  cases a <;> cases b <;> rfl

theorem apart_le_one (a b : Bool) : apart a b ≤ 1 := by
  cases a <;> cases b <;> decide

theorem apart_eq_one (a b : Bool) : apart a b = 1 ↔ a = !b := by
  cases a <;> cases b <;> decide

@[simp] theorem apart_not (a : Bool) : apart (!a) a = 1 := by cases a <;> rfl

theorem sum_eq_bound {n : ℕ} (f : Fin n → ℕ) (b : ℕ) (hf : ∀ i, f i ≤ b) :
    (∑ i, f i) = n * b ↔ ∀ i, f i = b := by
  have h := Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := f) (g := fun _ => b)
    (fun i _ => hf i)
  simpa using h

theorem path_bound (a x y b : Bool) : apart a x + apart x y + apart y b ≤ 2 + apart a b := by
  cases a <;> cases x <;> cases y <;> cases b <;> decide

theorem path_attains (a b : Bool) : apart a (!a) + apart (!a) a + apart a b = 2 + apart a b := by
  cases a <;> cases b <;> rfl

theorem triangle_bound (a b c : Bool) : apart a b + apart b c + apart a c ≤ 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem triangle_attains (a b c : Bool) :
    apart a b + apart b c + apart a c = 2 ↔ ¬ (a = b ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> decide

noncomputable def cutSet {n : ℕ} (ρ : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ρ v = true)

theorem cutSize_eq_sum {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    MaxCut.cutSize F S = ∑ e ∈ MaxCut.edges F, apart (decide (e.1 ∈ S)) (decide (e.2 ∈ S)) := by
  classical
  rw [MaxCut.cutSize, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h₁ : e.1 ∈ S <;> by_cases h₂ : e.2 ∈ S <;> simp [apart, h₁, h₂]

theorem decide_mem_cutSet {n : ℕ} (ρ : Fin n → Bool) (v : Fin n) :
    decide (v ∈ cutSet ρ) = ρ v := by
  cases hv : ρ v <;> simp [cutSet, hv]

theorem cutSize_cutSet {n : ℕ} (F : SimpleGraph (Fin n)) (ρ : Fin n → Bool) :
    MaxCut.cutSize F (cutSet ρ) = ∑ e ∈ MaxCut.edges F, apart (ρ e.1) (ρ e.2) := by
  rw [cutSize_eq_sum]
  simp only [decide_mem_cutSet]

theorem cutSize_le_maxCut {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    MaxCut.cutSize F S ≤ MaxCut.maxCut F :=
  Finset.le_sup (f := MaxCut.cutSize F) (Finset.mem_powerset.mpr (Finset.subset_univ S))

theorem exists_maxCut {n : ℕ} (F : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), MaxCut.cutSize F S = MaxCut.maxCut F := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin n)).powerset ⟨∅, Finset.empty_mem_powerset _⟩ (MaxCut.cutSize F)
  exact ⟨S, hS.symm⟩

theorem le_maxCut_iff {n : ℕ} (F : SimpleGraph (Fin n)) (k : ℕ) :
    k ≤ MaxCut.maxCut F ↔ ∃ S : Finset (Fin n), k ≤ MaxCut.cutSize F S := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := exists_maxCut F
    exact ⟨S, by simpa [hS] using h⟩
  · rintro ⟨S, hS⟩
    exact hS.trans (cutSize_le_maxCut F S)

end Lax222097Proofs.CutScores
