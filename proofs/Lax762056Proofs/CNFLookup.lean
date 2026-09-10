import Lax762056Proofs.CNFHead

namespace Lax762056Proofs.CNFLookup

open Lax979537Proofs StackProgram StackTransfer StackRepeat
open CNFPrefix CNFLiteral

variable {K Aux : Type} [DecidableEq K]

def program (counter src index : K) (j : Fin 3) : BitProgram K (Aux × Bool) :=
  .seq (repeatCount counter (skipNext src)) (CNFHead.program src index j.val)

theorem reorder (base : K → List Bool) (counter src index : K)
    (hci : counter ≠ index) (hsi : src ≠ index) (xs ys zs : List Bool)
    (a : Aux × Bool) (b : Option Bool) :
    working (Function.update base index zs) counter src xs ys a b =
      working (Function.update base counter xs) src index ys zs a b := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hc : k = counter <;> by_cases hs : k = src <;> by_cases hi : k = index <;>
      simp_all [working]

/-- Select a padded literal using a unary clause index and a fixed slot.
The counter is consumed, and the selected variable index and sign are
returned in a work stack and finite control. -/
theorem program_executes (base : K → List Bool) (counter src index : K)
    (hcs : counter ≠ src) (hci : counter ≠ index) (hsi : src ≠ index)
    (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) (a : Aux) (b : Option Bool) :
    let L := (ShortCNF.encode F).length
    let value := CNFHead.selected j.val (after i (some F)) (defaultLiteral j)
    ∃ c, c ≤ (2 * L + 5) * i + 15 * L + 35 ∧
      Executes (program counter src index j)
        (working (Function.update base index []) counter src (List.replicate i true)
          (ShortCNF.encode F) (a, (defaultLiteral j).2) b)
        (working (Function.update base counter []) src index
          (CNFHead.remainder j.val (after i (some F))) (List.replicate value.1 true) (a, value.2) none) c := by
  dsimp only
  obtain ⟨c, hc, hp⟩ := prefix_executes (Function.update base index []) counter src hcs
    i (ShortCNF.encode F).length (some F) (le_refl _) (a, (defaultLiteral j).2) b
  rw [reorder base counter src index hci hsi [] (contents (after i (some F))) []] at hp
  have hhead := CNFHead.program_executes (Function.update base counter []) src index hsi
    j.val (after i (some F)) a (defaultLiteral j) none
  have hbound : CNFHead.Bounded (some F) (ShortCNF.encode F).length := by
    intro G hG C hC l hl
    have hGF : F = G := by simpa using hG
    subst G
    exact (ShortCNF.index_lt F C l hC hl).le
  have hcHead := CNFHead.cost_bound j (after i (some F)) (ShortCNF.encode F).length
    (CNFHead.bounded_after hbound i)
  refine ⟨_, ?_, Executes.seq hp hhead⟩
  omega

def selected (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) : ShortCNF.Literal :=
  CNFHead.selected j.val (after i (some F)) (defaultLiteral j)

theorem selected_bound (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) :
    (selected F i j).1 < (ShortCNF.encode F).length := by
  have hB : CNFHead.Bounded (some F) ((ShortCNF.encode F).length - 1) := by
    intro G hG C hC l hl
    have hGF : F = G := by simpa using hG
    subst G
    have h := ShortCNF.index_lt F C l hC hl
    omega
  have h := CNFHead.selected_bound j (after i (some F)) ((ShortCNF.encode F).length - 1)
    (CNFHead.bounded_after hB i)
  have hp := ShortCNF.encode_pos F
  exact lt_of_le_of_lt h (by omega)

theorem selected_of_lt (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) (hi : i < F.length) :
    selected F i j = chosen j.val F[i] (defaultLiteral j) := by
  unfold selected
  rw [after_some F i hi.le]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem selected_of_ge (F : ShortCNF.Formula) (i : ℕ) (j : Fin 3) (hi : F.length ≤ i) :
    selected F i j = defaultLiteral j := by
  by_cases he : i = F.length
  · subst i
    simp [selected, after_some F F.length (le_refl _), CNFHead.selected]
  · rw [selected, after_past F i (by omega)]
    rfl

theorem selected_correct (F : ShortCNF.Formula) (hF : ShortCNF.Short F)
    (i : Fin (ShortCNF.encode F).length) (j : Fin 3) :
    ShortCNF.boundLiteral _ (ShortCNF.encode_pos F) (selected F i.val j) = ShortCNF.toThreeSAT F i j := by
  by_cases hi : i.val < F.length
  · rw [selected_of_lt F i.val j hi]
    have hmem : F[i.val] ∈ F := List.getElem_mem _
    have hn : F[i.val] ≠ [] := by
      have h := (hF _ hmem).1
      intro he
      simp [he] at h
    rw [chosen_triple _ _ _ hn]
    simp [ShortCNF.toThreeSAT, hi]
  · rw [selected_of_ge F i.val j (by omega), default_triple]
    simp [ShortCNF.toThreeSAT, hi]

end Lax762056Proofs.CNFLookup
