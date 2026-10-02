import Lax222097Proofs.CNFAtom
import Lax222097Proofs.CNFLookupStore

namespace Lax222097Proofs.CNFAtom

open Lax222097Proofs.QueryCompiler StackProgram StackTransfer StackBoolean

variable {K Aux : Type} [DecidableEq K]

theorem correct_literal {k : ℕ} (input : Inputs K k) (work : Work → K)
    (hi : Function.Injective work) (hf : ∀ w, input.Fresh (work w))
    (F : ShortCNF.Formula) (v : Fin k → Fin (ShortCNF.encode F).length) (s : EvalStore K Aux)
    (hc : Clean work s) (hr : Represents input F v s)
    (clause vertex : Fin k) (slot : Fin 3) (sign : Bool) :
    ∃ c, c ≤ cost.eval (ShortCNF.encode F).length ∧
      Returns (compile (.literal clause vertex slot sign) input work) s
        (value (.literal clause vertex slot sign) F v) c := by
  change ∀ w, s.stk (work w) = [] at hc
  have hne (i j : Work) (h : i ≠ j) : work i ≠ work j := fun he => h (hi he)
  have hcoord (w : Work) (i : Fin k) : input.coordinate i ≠ work w := Ne.symm ((hf w).2.2 i)
  have hword (w : Work) : input.word ≠ work w := Ne.symm (hf w).1
  let l := CNFLookup.selected F (v clause).val slot
  let r := CNFHead.remainder slot.val (CNFPrefix.after (v clause).val (some F))
  let s₁ := copied input.word (work .cursor) s
  let s₂ := copied (input.coordinate clause) (work .counter) s₁
  let s₃ := copied (input.coordinate vertex) (work .compare) s₂
  let s₄ := result (CNFLiteral.defaultLiteral slot).2 s₃
  have h₁ := StackCopy.copy_store input.word (work .cursor) (work .tmp)
    (hword _) (hword _) (hne _ _ (by decide)) s (hc _)
  have h₂ := StackCopy.copy_store (input.coordinate clause) (work .counter) (work .tmp)
    (hcoord _ _) (hcoord _ _) (hne _ _ (by decide)) s₁
    (by simp [s₁, copied, hne, hc])
  have h₃ := StackCopy.copy_store (input.coordinate vertex) (work .compare) (work .tmp)
    (hcoord _ _) (hcoord _ _) (hne _ _ (by decide)) s₂
    (by simp [s₂, s₁, copied, hne, hc])
  have h₄ := answer_returns (CNFLiteral.defaultLiteral slot).2 s₃
  obtain ⟨c, hcLookup, h₅⟩ := CNFLookup.lookup_store (work .counter) (work .cursor) (work .index)
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) F (v clause).val slot s₄
    (by simp [s₄, s₃, s₂, s₁, result, copied, hne, hc, hr.1])
    (by simp [s₄, s₃, s₂, s₁, result, copied, hne, hcoord, hc, hr.2.2])
    (by simp [s₄, s₃, s₂, s₁, result, copied, hne, hc]) rfl
  let s₅ : EvalStore K Aux :=
    ⟨((s₄.state.1.1, l.2), none),
      Function.update (Function.update (Function.update s₄.stk (work .counter) [])
        (work .cursor) r) (work .index) (List.replicate l.1 true)⟩
  let s₆ : EvalStore K Aux := ⟨(((s₅.state.1.1.1, decide (s₅.state.1.2 = sign)), false), none), s₅.stk⟩
  have h₆ := Executes.atom
    (.load (fun q : ((Aux × Bool) × Bool) × Option Bool =>
      (((q.1.1.1, decide (q.1.2 = sign)), false), none))) s₅
  have hindex : (s₆.stk (work .index)).length = l.1 := by simp [s₆, s₅]
  have hcompare : (s₆.stk (work .compare)).length = (v vertex).val := by
    simp [s₆, s₅, s₄, s₃, s₂, s₁, result, copied, hne, hcoord, hc, hr.2.2]
  obtain ⟨d, hdCompare, h₇⟩ := StackEqual.equal_store (work .index) (work .compare)
    (hne _ _ (by decide)) s₆
  let s₇ : EvalStore K Aux :=
    ⟨((s₆.state.1.1, decide ((s₆.stk (work .index)).length = (s₆.stk (work .compare)).length)), none),
      Function.update (Function.update s₆.stk (work .index) []) (work .compare) []⟩
  have hcursor : s₇.stk (work .cursor) = r := by simp [s₇, s₆, s₅, hne]
  have h₈ := StackClear.clear_store (work .cursor) s₇
  let s₈ : EvalStore K Aux := ⟨(s₇.state.1, none), Function.update s₇.stk (work .cursor) []⟩
  have h₉ := Executes.atom
    (.load (fun q : ((Aux × Bool) × Bool) × Option Bool =>
      (((q.1.1.1, true), q.1.1.2 && q.1.2), none))) s₈
  have hend : Op.apply
      (.load (fun q : ((Aux × Bool) × Bool) × Option Bool =>
        (((q.1.1.1, true), q.1.1.2 && q.1.2), none))) s₈ =
      result (value (.literal clause vertex slot sign) F v) s := by
    apply Store.ext
    · simp only [Op.apply, s₈, s₇, hindex, hcompare]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, copied, result, value, l, Bool.and_comm]
    · funext key
      by_cases hcu : key = work .cursor
      · subst key; simp [Op.apply, s₈, result, hc]
      · by_cases hco : key = work .counter
        · subst key
          simp [Op.apply, s₈, s₇, s₆, s₅, result, hne, hc]
        · by_cases hix : key = work .index
          · subst key
            simp [Op.apply, s₈, s₇, result, hne, hc]
          · by_cases hcp : key = work .compare
            · subst key
              simp [Op.apply, s₈, s₇, result, hne, hc]
            · simp [Op.apply, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, copied, result, hcu, hco, hix, hcp]
  rw [hend] at h₉
  have h := Executes.seq h₁ (Executes.seq h₂ (Executes.seq h₃ (Executes.seq h₄
    (Executes.seq h₅ (Executes.seq h₆ (Executes.seq h₇ (Executes.seq h₈ h₉)))))))
  refine ⟨_, ?_, h⟩
  have hlen₁ : (s.stk input.word).length = (ShortCNF.encode F).length := by rw [hr.1]
  have hlen₂ : (s₁.stk (input.coordinate clause)).length = (v clause).val := by
    simp [s₁, copied, hcoord, hr.2.2]
  have hlen₃ : (s₂.stk (input.coordinate vertex)).length = (v vertex).val := by
    simp [s₂, s₁, copied, hcoord, hr.2.2]
  have hrBound : r.length ≤ (ShortCNF.encode F).length :=
    (CNFHead.remainder_length slot.val _).trans (CNFHead.after_length (some F) (v clause).val)
  have hlBound : l.1 < (ShortCNF.encode F).length := CNFLookup.selected_bound F _ slot
  have hv₁ := (v clause).isLt
  have hv₂ := (v vertex).isLt
  have hm := Nat.mul_le_mul_left (2 * (ShortCNF.encode F).length + 5) (Nat.le_of_lt hv₁)
  rw [hindex, hcompare] at hdCompare
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hlen₁, hlen₂, hlen₃, hcursor]
  nlinarith

theorem compile_correct {k : ℕ} (test : Test k) (input : Inputs K k) (work : Work → K)
    (hi : Function.Injective work) (hf : ∀ w, input.Fresh (work w))
    (F : ShortCNF.Formula) (v : Fin k → Fin (ShortCNF.encode F).length) (s : EvalStore K Aux)
    (hc : Clean work s) (hr : Represents input F v s) :
    ∃ c, c ≤ cost.eval (ShortCNF.encode F).length ∧ Returns (compile test input work) s (value test F v) c := by
  cases test with
  | constant b =>
    refine ⟨1, ?_, answer_returns b s⟩
    simp [cost]
  | equal x y => exact correct_equal input work hi hf F v s hc hr x y
  | literal c x j sign => exact correct_literal input work hi hf F v s hc hr c x j sign

end Lax222097Proofs.CNFAtom
