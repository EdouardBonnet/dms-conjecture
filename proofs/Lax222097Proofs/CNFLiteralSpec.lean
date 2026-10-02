import Lax222097Proofs.CNFLiteral

namespace Lax222097Proofs.CNFLiteral

theorem chosen_bound (k : ℕ) (C : ShortCNF.Clause) (old : ShortCNF.Literal) (L : ℕ)
    (hC : ∀ l ∈ C, l.1 ≤ L) (ho : old.1 ≤ L) : (chosen k C old).1 ≤ L := by
  induction k generalizing C old with
  | zero =>
    cases C with
    | nil => exact ho
    | cons l C => exact hC l (by simp)
  | succ k ih =>
    cases C with
    | nil => exact ho
    | cons l C => exact ih C l (fun v hv => hC v (by simp [hv])) (hC l (by simp))

theorem rest_length (k : ℕ) (C : ShortCNF.Clause) (tail : List Bool) :
    (rest k C tail).length ≤ (ShortCNF.encodeClause C).length + tail.length := by
  induction k generalizing C with
  | zero =>
    cases C <;> simp [rest, ShortCNF.encodeClause, ShortCNF.encodeList]
    omega
  | succ k ih =>
    cases C with
    | nil => simp [rest, ShortCNF.encodeClause, ShortCNF.encodeList]
    | cons l C =>
      have h := ih C
      simp only [ShortCNF.encodeClause] at h
      simp only [rest, ShortCNF.encodeClause, ShortCNF.encodeList, List.length_cons,
        List.length_append]
      change (rest k C tail).length ≤ _
      omega

theorem chosen_triple (n : ℕ) (hn : 0 < n) (C : ShortCNF.Clause) (hC : C ≠ [])
    (j : Fin 3) (old : ShortCNF.Literal) :
    ShortCNF.boundLiteral n hn (chosen j.val C old) =
      ShortCNF.triple ⟨0, hn⟩ (C.map (ShortCNF.boundLiteral n hn)) j := by
  rcases C with _ | ⟨a, C⟩
  · exact False.elim (hC rfl)
  rcases C with _ | ⟨b, C⟩
  · fin_cases j <;> rfl
  rcases C with _ | ⟨c, C⟩
  · fin_cases j <;> rfl
  fin_cases j <;> rfl

def defaultLiteral (j : Fin 3) : ShortCNF.Literal := (0, decide (j ≠ 1))

theorem default_triple (n : ℕ) (hn : 0 < n) (j : Fin 3) :
    ShortCNF.boundLiteral n hn (defaultLiteral j) = ShortCNF.triple ⟨0, hn⟩ [] j := by
  fin_cases j <;> simp [defaultLiteral, ShortCNF.boundLiteral, ShortCNF.triple, hn]

theorem literal_time_bound (j : Fin 3) (C : ShortCNF.Clause) (L : ℕ)
    (hC : ∀ l ∈ C, l.1 ≤ L) : time j.val C (defaultLiteral j) ≤ 15 * L + 30 := by
  have h := time_bound j.val C (defaultLiteral j) L hC (Nat.zero_le _)
  have hj := j.isLt
  nlinarith

end Lax222097Proofs.CNFLiteral
