import Lax762056Proofs.SubdividedCut

namespace Lax762056Proofs.SubdividedLabels

open SubdividedCut

abbrev Vertex (n m : ℕ) := Fin n ⊕ (Fin m × Bool)

def number {n m : ℕ} : Vertex n m → Fin (n + 2 * m)
  | .inl v => core m v
  | .inr (e, b) => middle n e b

def unnumber {n m : ℕ} (v : Fin (n + 2 * m)) : Vertex n m :=
  if h : v.val < n then .inl ⟨v.val, h⟩
  else .inr (⟨(v.val - n) / 2, by omega⟩, decide ((v.val - n) % 2 = 1))

theorem unnumber_number {n m : ℕ} (v : Vertex n m) : unnumber (number v) = v := by
  rcases v with v | ⟨e, b⟩
  · simp [unnumber, number, core]
  · cases b <;> simp [unnumber, number, middle]
    have hnot : ¬ n + 2 * e.val + 1 < n := by omega
    simp [hnot, Nat.add_assoc, Nat.add_div]

theorem number_unnumber {n m : ℕ} (v : Fin (n + 2 * m)) : number (unnumber v) = v := by
  unfold unnumber
  split
  · rfl
  · apply Fin.ext
    simp only [number, middle]
    split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> omega

def equiv (n m : ℕ) : Vertex n m ≃ Fin (n + 2 * m) where
  toFun := number
  invFun := unnumber
  left_inv := unnumber_number
  right_inv := number_unnumber

theorem core_injective {n m : ℕ} : Function.Injective (core m : Fin n → Fin (n + 2 * m)) := by
  intro x y h
  apply Fin.ext
  exact congrArg (fun u : Fin (n + 2 * m) => u.val) h

theorem middle_injective {n m : ℕ} :
    Function.Injective (fun p : Fin m × Bool => middle n p.1 p.2) := by
  intro x y h
  have he := (equiv n m).injective (a₁ := .inr x) (a₂ := .inr y) h
  exact Sum.inr.inj he

@[simp] theorem core_eq {n m : ℕ} (x y : Fin n) : core m x = core m y ↔ x = y :=
  core_injective.eq_iff

@[simp] theorem middle_eq {n m : ℕ} (e f : Fin m) (b d : Bool) :
    middle n e b = middle n f d ↔ e = f ∧ b = d := by
  constructor
  · intro h
    have he := middle_injective (n := n) (a₁ := (e, b)) (a₂ := (f, d)) h
    exact Prod.mk.inj he
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem core_ne_middle {n m : ℕ} (v : Fin n) (e : Fin m) (b : Bool) : core m v ≠ middle n e b := by
  intro h
  have he := (equiv n m).injective (a₁ := .inl v) (a₂ := .inr (e, b)) h
  cases he

@[simp] theorem middle_ne_core {n m : ℕ} (v : Fin n) (e : Fin m) (b : Bool) : middle n e b ≠ core m v :=
  Ne.symm (core_ne_middle v e b)

theorem core_core {n m : ℕ} (l r : Fin m → Fin n) (x y : Fin n) :
    ¬ (graph l r).Adj (core m x) (core m y) := by
  rintro ⟨_, h⟩
  rcases h with ⟨⟨e, j⟩, he⟩ | ⟨⟨e, j⟩, he⟩ <;>
    fin_cases j <;> simp [edgePair] at he

theorem core_middle {n m : ℕ} (l r : Fin m → Fin n) (x : Fin n) (e : Fin m) (b : Bool) :
    (graph l r).Adj (core m x) (middle n e b) ↔ x = if b then r e else l e := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h⟩
    rcases h with ⟨⟨f, j⟩, he⟩ | ⟨⟨f, j⟩, he⟩ <;> fin_cases j <;> simp [edgePair] at he
    all_goals rcases he with ⟨h₁, h₂, h₃⟩; subst f; subst b; exact h₁
  · intro h
    refine ⟨core_ne_middle _ _ _, ?_⟩
    cases b
    · exact Or.inl ⟨(e, 0), by simpa [edgePair] using h⟩
    · exact Or.inl ⟨(e, 2), by simpa [edgePair] using h⟩

theorem middle_middle {n m : ℕ} (l r : Fin m → Fin n) (e f : Fin m) (b d : Bool) :
    (graph l r).Adj (middle n e b) (middle n f d) ↔ e = f ∧ b ≠ d := by
  constructor
  · rintro ⟨_, h⟩
    rcases h with ⟨⟨g, j⟩, he⟩ | ⟨⟨g, j⟩, he⟩ <;> fin_cases j <;> simp [edgePair] at he
    all_goals aesop
  · rintro ⟨rfl, hbd⟩
    cases b <;> cases d <;> simp at hbd
    · rw [graph, SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨(e, 1), by simp [edgePair]⟩⟩
    · rw [graph, SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inr ⟨(e, 1), by simp [edgePair]⟩⟩

end Lax762056Proofs.SubdividedLabels
