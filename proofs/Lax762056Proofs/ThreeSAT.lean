import Lax762056Proofs.NAEMaxCut

/-! Three-literal clauses suffice for the anticipated Cook–Levin dependency:
its circuit compiler outputs Tseitin clauses, each with one to three literals.
Unit and binary clauses can be padded by repeating their final literal. -/

namespace Lax762056Proofs.ThreeSAT

open Lax762056 NAEMaxCut

variable {n m : ℕ}

def Satisfiable (C : Formula n m) : Prop :=
  ∃ ρ : Fin n → Bool, ∀ i, (eval ρ (C i 0) || eval ρ (C i 1) || eval ρ (C i 2)) = true

def NAE (a b c : Bool) : Prop := ¬ (a = b ∧ b = c)

theorem gadget (a b c s : Bool) (h₁ : NAE a b s) (h₂ : NAE (!s) c false) :
    (a || b || c) = true := by
  cases a <;> cases b <;> cases c <;> cases s <;> simp_all [NAE]

theorem gadget_first (a b : Bool) : NAE a b (!(a || b)) := by
  cases a <;> cases b <;> simp [NAE]

theorem gadget_second (a b c : Bool) (h : (a || b || c) = true) :
    NAE (!(!(a || b))) c false := by
  cases a <;> cases b <;> cases c <;> simp_all [NAE]

theorem nae_not (a b c : Bool) : NAE (!a) (!b) (!c) ↔ NAE a b c := by
  cases a <;> cases b <;> cases c <;> simp [NAE]

theorem eval_not {k : ℕ} (ρ : Fin k → Bool) (t : Literal k) :
    eval (fun v => !ρ v) t = !eval ρ t := by
  rcases t with ⟨v, b⟩
  cases b <;> simp [eval]

def old (m : ℕ) (v : Fin n) : Fin (n + 1 + m) := ⟨v.val, by omega⟩

def anchor (n m : ℕ) : Fin (n + 1 + m) := ⟨n, by omega⟩

def auxiliary (n : ℕ) (i : Fin m) : Fin (n + 1 + m) := ⟨n + 1 + i.val, by omega⟩

def oldLiteral (m : ℕ) (t : Literal n) : Literal (n + 1 + m) := (old m t.1, t.2)

def toNAE (C : Formula n m) : Formula (n + 1 + m) (m * 2) := fun j k =>
  let p : Fin m × Fin 2 := finProdFinEquiv.symm j
  if p.2 = 0 then
    if k = 0 then oldLiteral m (C p.1 0)
    else if k = 1 then oldLiteral m (C p.1 1) else (auxiliary n p.1, true)
  else
    if k = 0 then (auxiliary n p.1, false)
    else if k = 1 then oldLiteral m (C p.1 2) else (anchor n m, true)

def extend (C : Formula n m) (ρ : Fin n → Bool) (v : Fin (n + 1 + m)) : Bool :=
  if hv : v.val < n then ρ ⟨v.val, hv⟩
  else if he : v.val = n then false
  else
    let i : Fin m := ⟨v.val - (n + 1), by omega⟩
    !(eval ρ (C i 0) || eval ρ (C i 1))

theorem extend_old (C : Formula n m) (ρ : Fin n → Bool) (v : Fin n) :
    extend C ρ (old m v) = ρ v := by simp [extend, old]

theorem extend_anchor (C : Formula n m) (ρ : Fin n → Bool) :
    extend C ρ (anchor n m) = false := by simp [extend, anchor]

theorem extend_auxiliary (C : Formula n m) (ρ : Fin n → Bool) (i : Fin m) :
    extend C ρ (auxiliary n i) = !(eval ρ (C i 0) || eval ρ (C i 1)) := by
  have h₁ : ¬ (auxiliary n i).val < n := by simp [auxiliary]; omega
  have h₂ : (auxiliary n i).val ≠ n := by simp [auxiliary]; omega
  rw [extend, dif_neg h₁, dif_neg h₂]
  simp [auxiliary]

theorem eval_old (ρ : Fin (n + 1 + m) → Bool) (t : Literal n) :
    eval ρ (oldLiteral m t) = eval (fun v => ρ (old m v)) t := rfl

theorem extend_eval_old (C : Formula n m) (ρ : Fin n → Bool) (t : Literal n) :
    eval (extend C ρ) (oldLiteral m t) = eval ρ t := by
  simp [eval_old, extend_old]

theorem complete (C : Formula n m) (ρ : Fin n → Bool)
    (hρ : ∀ i, (eval ρ (C i 0) || eval ρ (C i 1) || eval ρ (C i 2)) = true) :
    ∀ j, NAE (eval (extend C ρ) (toNAE C j 0)) (eval (extend C ρ) (toNAE C j 1))
      (eval (extend C ρ) (toNAE C j 2)) := by
  intro j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k
  · simpa [toNAE, eval, oldLiteral, extend_old, extend_auxiliary] using
      gadget_first (eval ρ (C i 0)) (eval ρ (C i 1))
  · simpa [toNAE, eval, oldLiteral, extend_old, extend_auxiliary, extend_anchor] using
      gadget_second (eval ρ (C i 0)) (eval ρ (C i 1)) (eval ρ (C i 2)) (hρ i)

theorem sound (C : Formula n m) (ρ : Fin (n + 1 + m) → Bool) (ha : ρ (anchor n m) = false)
    (hρ : ∀ j, NAE (eval ρ (toNAE C j 0)) (eval ρ (toNAE C j 1)) (eval ρ (toNAE C j 2))) :
    ∀ i, (eval (fun v => ρ (old m v)) (C i 0) || eval (fun v => ρ (old m v)) (C i 1) ||
      eval (fun v => ρ (old m v)) (C i 2)) = true := by
  intro i
  have h₁ := hρ (finProdFinEquiv (i, (0 : Fin 2)))
  have h₂ := hρ (finProdFinEquiv (i, (1 : Fin 2)))
  simp only [toNAE, Equiv.symm_apply_apply] at h₁ h₂
  simp [eval_old, eval, ha] at h₁ h₂
  exact gadget _ _ _ _ h₁ h₂

theorem reduction_correct (C : Formula n m) : Satisfiable C ↔ NAEMaxCut.Satisfiable (toNAE C) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨extend C ρ, complete C ρ hρ⟩
  · rintro ⟨ρ, hρ⟩
    by_cases ha : ρ (anchor n m) = false
    · exact ⟨fun v => ρ (old m v), sound C ρ ha hρ⟩
    · have ha' : (!ρ (anchor n m)) = false := by cases hb : ρ (anchor n m) <;> simp_all
      have hn : ∀ j, NAE (eval (fun v => !ρ v) (toNAE C j 0))
          (eval (fun v => !ρ v) (toNAE C j 1)) (eval (fun v => !ρ v) (toNAE C j 2)) := by
        intro j
        simp only [eval_not]
        exact (nae_not _ _ _).mpr (hρ j)
      exact ⟨fun v => !ρ (old m v), sound C (fun v => !ρ v) ha' hn⟩

def toMaxCut (C : Formula n m) : GraphEncoding.Instance := NAEMaxCut.toMaxCut (toNAE C)

theorem maxCut_correct (C : Formula n m) :
    Satisfiable C ↔ (toMaxCut C).threshold ≤ MaxCut.maxCut (toMaxCut C).graph :=
  (reduction_correct C).trans (NAEMaxCut.instance_correct (toNAE C))

theorem maxCut_order (C : Formula n m) : (toMaxCut C).order = 4 * n + 16 * m + 4 := by
  rw [toMaxCut, NAEMaxCut.instance_order]
  omega

theorem maxCut_threshold (C : Formula n m) : (toMaxCut C).threshold = 3 * n + 19 * m + 3 := by
  rw [toMaxCut, NAEMaxCut.instance_threshold]
  omega

end Lax762056Proofs.ThreeSAT
