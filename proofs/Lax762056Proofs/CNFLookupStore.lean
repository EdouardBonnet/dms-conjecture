import Lax762056Proofs.CNFLookup

namespace Lax762056Proofs.CNFLookup

open Lax979537Proofs StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

theorem lookup_store (counter src index : K)
    (hcs : counter ≠ src) (hci : counter ≠ index) (hsi : src ≠ index)
    (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) (s : BitStore K (Aux × Bool))
    (hs : s.stk src = ShortCNF.encode F) (hc : s.stk counter = List.replicate i true)
    (hi : s.stk index = []) (hb : s.state.1.2 = (CNFLiteral.defaultLiteral j).2) :
    let L := (ShortCNF.encode F).length
    ∃ c, c ≤ (2 * L + 5) * i + 15 * L + 35 ∧
      Executes (program counter src index j) s
        ⟨((s.state.1.1, (selected F i j).2), none),
          Function.update (Function.update (Function.update s.stk counter []) src
            (CNFHead.remainder j.val (CNFPrefix.after i (some F)))) index
              (List.replicate (selected F i j).1 true)⟩ c := by
  obtain ⟨c, hcBound, h⟩ := program_executes s.stk counter src index hcs hci hsi
    F i j s.state.1.1 s.state.2
  have hin : working (Function.update s.stk index []) counter src (List.replicate i true)
      (ShortCNF.encode F) (s.state.1.1, (CNFLiteral.defaultLiteral j).2) s.state.2 = s := by
    apply Store.ext
    · simp [working, ← hb]
    · funext key
      by_cases hc' : key = counter
      · subst key; simp [working, hcs, hc]
      · by_cases hs' : key = src
        · subst key; simp [working, hs]
        · by_cases hi' : key = index
          · subst key; simp [working, Ne.symm hsi, Ne.symm hci, hi]
          · simp [working, hc', hs', hi']
  rw [hin] at h
  exact ⟨c, hcBound, h⟩

end Lax762056Proofs.CNFLookup
