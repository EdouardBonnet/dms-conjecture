import Lax222097Proofs.CNFLiteralSpec

set_option backward.isDefEq.respectTransparency false

namespace Lax222097Proofs.CNFHead

open Lax222097Proofs.QueryCompiler StackProgram StackTransfer CNFLiteral CNFPrefix

variable {K Aux : Type} [DecidableEq K]

def selected (k : ℕ) (F : Option ShortCNF.Formula) (old : ShortCNF.Literal) : ShortCNF.Literal :=
  match F with
  | some (C :: _) => chosen k C old
  | _ => old

def remainder (k : ℕ) (F : Option ShortCNF.Formula) : List Bool :=
  match F with
  | some (C :: F) => rest k C (ShortCNF.encode F)
  | _ => []

def cost (k : ℕ) (F : Option ShortCNF.Formula) (old : ShortCNF.Literal) : ℕ :=
  match F with
  | some (C :: _) => 2 + time k C old
  | _ => 3

def program (src index : K) (k : ℕ) : BitProgram K (Aux × Bool) :=
  .seq (read src) (.branch (fun s => s.2 == some true) (readAt src index k) CNFScan.reset)

theorem program_executes (base : K → List Bool) (src index : K) (hne : src ≠ index)
    (k : ℕ) (F : Option ShortCNF.Formula) (a : Aux) (old : ShortCNF.Literal) (b : Option Bool) :
    Executes (program src index k)
      (working base src index (contents F) (List.replicate old.1 true) (a, old.2) b)
      (working base src index (remainder k F) (List.replicate (selected k F old).1 true)
        (a, (selected k F old).2) none) (cost k F old) := by
  rcases F with _ | F
  · exact Executes.seq (read_src base src index hne [] _ a old.2 b)
      (Executes.branch_false rfl (reset_working base src index [] _ a old.2 none))
  cases F with
  | nil =>
    exact Executes.seq (read_src base src index hne [false] _ a old.2 b)
      (Executes.branch_false rfl (reset_working base src index [] _ a old.2 (some false)))
  | cons C F =>
    have hl := readAt_executes base src index hne k C (ShortCNF.encode F) a old (some true)
    have hr := read_src base src index hne
      (true :: (ShortCNF.encodeClause C ++ ShortCNF.encode F)) (List.replicate old.1 true) a old.2 b
    have h := Executes.seq hr (Executes.branch_true (q := CNFScan.reset)
      (b := fun s : (Aux × Bool) × Option Bool => s.2 == some true) rfl hl)
    convert! h using 1 <;> simp [cost] <;> omega

theorem remainder_length (k : ℕ) (F : Option ShortCNF.Formula) :
    (remainder k F).length ≤ (contents F).length := by
  rcases F with _ | F
  · rfl
  cases F with
  | nil => simp [remainder]
  | cons C F =>
    have h := rest_length k C (ShortCNF.encode F)
    simp only [remainder, contents, ShortCNF.encode, ShortCNF.encodeList, List.length_cons,
      List.length_append] at h ⊢
    omega

def Bounded (F : Option ShortCNF.Formula) (L : ℕ) : Prop :=
  ∀ G ∈ F, ∀ C ∈ G, ∀ l ∈ C, l.1 ≤ L

theorem cost_bound (j : Fin 3) (F : Option ShortCNF.Formula) (L : ℕ)
    (hF : Bounded F L) : cost j.val F (defaultLiteral j) ≤ 15 * L + 33 := by
  rcases F with _ | F
  · simp [cost]
  cases F with
  | nil => simp [cost]
  | cons C F =>
    have h := literal_time_bound j C L (hF (C :: F) (by simp) C (by simp))
    simp only [cost]
    omega

theorem selected_bound (j : Fin 3) (F : Option ShortCNF.Formula) (L : ℕ)
    (hF : Bounded F L) : (selected j.val F (defaultLiteral j)).1 ≤ L := by
  rcases F with _ | F
  · exact Nat.zero_le _
  cases F with
  | nil => exact Nat.zero_le _
  | cons C F =>
    exact chosen_bound _ _ _ _ (hF (C :: F) (by simp) C (by simp)) (Nat.zero_le _)

theorem bounded_next {F : Option ShortCNF.Formula} {L : ℕ} (h : Bounded F L) : Bounded (next F) L := by
  rcases F with _ | F
  · simpa [next] using h
  cases F with
  | nil => simp [Bounded, next]
  | cons C F =>
    intro G hG D hD l hl
    have heq : F = G := by simpa [next] using hG
    subst G
    exact h (C :: F) (by simp) D (by simp [hD]) l hl

theorem bounded_after {F : Option ShortCNF.Formula} {L : ℕ} (h : Bounded F L) (i : ℕ) :
    Bounded (after i F) L := by
  induction i generalizing F with
  | zero => exact h
  | succ i ih => exact ih (bounded_next h)

theorem after_length (F : Option ShortCNF.Formula) (i : ℕ) :
    (contents (after i F)).length ≤ (contents F).length := by
  induction i generalizing F with
  | zero => rfl
  | succ i ih => exact (ih (next F)).trans (next_length F)

end Lax222097Proofs.CNFHead
