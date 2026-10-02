import Lax222097Proofs.QueryLoop

namespace Lax222097Proofs.QueryProgram

open Lax222097Proofs.QueryCompiler StackProgram

theorem execution_length {K σ : Type} {Γ : K → Type} [DecidableEq K]
    {p : Program Γ σ} {s t : Store Γ σ} {c : ℕ} (h : Executes p s t c) (key : K) :
    (t.stk key).length ≤ (s.stk key).length + c := by
  induction h with
  | atom op s =>
      cases op with
      | push k f =>
          by_cases hk : key = k
          · subst key; simp [Op.apply]
          · simp [Op.apply, hk]
      | pop k f =>
          by_cases hk : key = k
          · subst key; simp [Op.apply]; omega
          · simp [Op.apply, hk]
      | peek k f | load f => simp [Op.apply]
  | seq hp hq ihp ihq => omega
  | branch_true hb hp ih | branch_false hb hp ih => omega
  | loop_false hb => omega
  | loop_true hb hp hq ihp ihq => omega

end Lax222097Proofs.QueryProgram
