import Lax762056Proofs.SubdividedCut
import Mathlib.Logic.Equiv.Fin.Basic

/-! The semantic reduction from not-all-equal 3-SAT to simple unweighted
Max Cut. Repeated literals, tautologies, and empty formulas are allowed. -/

namespace Lax762056Proofs.NAEMaxCut

open Lax762056 CutScores

variable {n m : ℕ}

abbrev Literal (n : ℕ) := Fin n × Bool
abbrev Formula (n m : ℕ) := Fin m → Fin 3 → Literal n

def eval (ρ : Fin n → Bool) (t : Literal n) : Bool := if t.2 then ρ t.1 else !ρ t.1

def Satisfiable (C : Formula n m) : Prop :=
  ∃ ρ : Fin n → Bool, ∀ i, ¬ (eval ρ (C i 0) = eval ρ (C i 1) ∧
    eval ρ (C i 1) = eval ρ (C i 2))

def index (t : Literal n) : Fin (2 * n) :=
  ⟨2 * t.1.val + (if t.2 then 1 else 0), by rcases t with ⟨v, b⟩; cases b <;> simp <;> omega⟩

def assignment (ρ : Fin n → Bool) (v : Fin (2 * n)) : Bool :=
  if v.val % 2 = 1 then ρ ⟨v.val / 2, by omega⟩ else !ρ ⟨v.val / 2, by omega⟩

theorem assignment_index (ρ : Fin n → Bool) (t : Literal n) : assignment ρ (index t) = eval ρ t := by
  rcases t with ⟨v, b⟩
  cases b <;> simp [assignment, index, eval, Nat.add_div]

abbrev Edge (n m : ℕ) := Fin n ⊕ (Fin m × Fin 3)

def edgeEquiv (n m : ℕ) : Edge n m ≃ Fin (n + m * 3) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def pair (C : Formula n m) : Edge n m → Literal n × Literal n
  | .inl v => ((v, false), (v, true))
  | .inr (i, j) => if j = 0 then (C i 0, C i 1)
    else if j = 1 then (C i 1, C i 2) else (C i 0, C i 2)

def left (C : Formula n m) (e : Fin (n + m * 3)) : Fin (2 * n) :=
  index (pair C ((edgeEquiv n m).symm e)).1

def right (C : Formula n m) (e : Fin (n + m * 3)) : Fin (2 * n) :=
  index (pair C ((edgeEquiv n m).symm e)).2

def variableScore (χ : Fin (2 * n) → Bool) (v : Fin n) : ℕ :=
  apart (χ (index (v, false))) (χ (index (v, true)))

def clauseScore (C : Formula n m) (χ : Fin (2 * n) → Bool) (i : Fin m) : ℕ :=
  apart (χ (index (C i 0))) (χ (index (C i 1))) +
    apart (χ (index (C i 1))) (χ (index (C i 2))) +
    apart (χ (index (C i 0))) (χ (index (C i 2)))

theorem score_eq (C : Formula n m) (χ : Fin (2 * n) → Bool) :
    SubdividedCut.score (left C) (right C) χ =
      (∑ v, variableScore χ v) + ∑ i, clauseScore C χ i := by
  unfold SubdividedCut.score
  calc
    _ = ∑ e : Edge n m, apart (χ (index (pair C e).1)) (χ (index (pair C e).2)) := by
      symm
      apply Fintype.sum_equiv (edgeEquiv n m)
      intro e
      simp [left, right]
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp [pair, Fin.sum_univ_three, variableScore, clauseScore, Nat.add_assoc]

theorem variable_le (χ : Fin (2 * n) → Bool) (v : Fin n) : variableScore χ v ≤ 1 := apart_le_one _ _

theorem clause_le (C : Formula n m) (χ : Fin (2 * n) → Bool) (i : Fin m) :
    clauseScore C χ i ≤ 2 := triangle_bound _ _ _

theorem score_attains_iff (C : Formula n m) (χ : Fin (2 * n) → Bool) :
    n + 2 * m ≤ SubdividedCut.score (left C) (right C) χ ↔
      (∀ v, variableScore χ v = 1) ∧ (∀ i, clauseScore C χ i = 2) := by
  rw [score_eq]
  have hv : (∑ v, variableScore χ v) ≤ n := by
    calc
      _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun v _ => variable_le χ v)
      _ = _ := by simp
  have hc : (∑ i, clauseScore C χ i) ≤ 2 * m := by
    calc
      _ ≤ ∑ _ : Fin m, 2 := Finset.sum_le_sum (fun i _ => clause_le C χ i)
      _ = _ := by simp [Nat.mul_comm]
  have hviff := sum_eq_bound (variableScore χ) 1 (variable_le χ)
  have hciff := sum_eq_bound (clauseScore C χ) 2 (clause_le C χ)
  simp only [Nat.mul_one, Nat.mul_comm m 2] at hviff hciff
  constructor
  · intro h
    exact ⟨hviff.mp (by omega), hciff.mp (by omega)⟩
  · rintro ⟨h₁, h₂⟩
    rw [hviff.mpr h₁, hciff.mpr h₂]

theorem literal_agreement (χ : Fin (2 * n) → Bool) (hχ : ∀ v, variableScore χ v = 1)
    (t : Literal n) : eval (fun v => χ (index (v, true))) t = χ (index t) := by
  rcases t with ⟨v, b⟩
  cases b with
  | false =>
      have h := (apart_eq_one _ _).mp (hχ v)
      exact h.symm
  | true => rfl

theorem satisfiable_iff_score (C : Formula n m) :
    Satisfiable C ↔ ∃ χ : Fin (2 * n) → Bool,
      n + 2 * m ≤ SubdividedCut.score (left C) (right C) χ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨assignment ρ, (score_attains_iff C _).mpr ⟨?_, ?_⟩⟩
    · intro v
      simp [variableScore, assignment_index, eval]
    · intro i
      unfold clauseScore
      simp only [assignment_index]
      exact (triangle_attains _ _ _).mpr (hρ i)
  · rintro ⟨χ, hχ⟩
    obtain ⟨hv, hc⟩ := (score_attains_iff C χ).mp hχ
    refine ⟨fun v => χ (index (v, true)), ?_⟩
    intro i
    simp only [literal_agreement χ hv]
    exact (triangle_attains _ _ _).mp (hc i)

def toMaxCut (C : Formula n m) : GraphEncoding.Instance where
  order := 2 * n + 2 * (n + m * 3)
  graph := SubdividedCut.graph (left C) (right C)
  threshold := 2 * (n + m * 3) + (n + 2 * m)

theorem instance_correct (C : Formula n m) :
    Satisfiable C ↔ (toMaxCut C).threshold ≤ MaxCut.maxCut (toMaxCut C).graph := by
  rw [satisfiable_iff_score]
  exact (SubdividedCut.reduction_iff (left C) (right C) (n + 2 * m)).symm

theorem instance_order (C : Formula n m) : (toMaxCut C).order = 4 * n + 6 * m := by
  dsimp [toMaxCut]
  omega

theorem instance_threshold (C : Formula n m) : (toMaxCut C).threshold = 3 * n + 8 * m := by
  dsimp [toMaxCut]
  omega

end Lax762056Proofs.NAEMaxCut
