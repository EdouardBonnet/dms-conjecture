import Lax762056Proofs.CNFLookup
import Lax762056Proofs.StackEqual
import Lax762056Proofs.StackCount
import Lax762056Proofs.QueryCompiler.StackBoolean

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.CNFAtom

open Lax762056Proofs.QueryCompiler StackProgram StackTransfer StackBoolean

inductive Test (k : ℕ)
  | constant (b : Bool)
  | equal (x y : Fin k)
  | literal (clause vertex : Fin k) (slot : Fin 3) (sign : Bool)

inductive Work
  | cursor | counter | index | compare | tmp
  deriving DecidableEq, Fintype

structure Inputs (K : Type) (k : ℕ) where
  word : K
  domain : K
  coordinate : Fin k → K

def Inputs.Fresh {K : Type} {k : ℕ} (input : Inputs K k) (key : K) : Prop :=
  key ≠ input.word ∧ key ≠ input.domain ∧ ∀ i, key ≠ input.coordinate i

def Represents {K Aux : Type} {k : ℕ} (input : Inputs K k) (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (s : EvalStore K Aux) : Prop :=
  s.stk input.word = ShortCNF.encode F ∧
    s.stk input.domain = List.replicate (ShortCNF.encode F).length true ∧
      ∀ i, s.stk (input.coordinate i) = List.replicate (v i).val true

def Clean {K Aux : Type} (work : Work → K) (s : EvalStore K Aux) : Prop := ∀ w, s.stk (work w) = []

def value {k : ℕ} (test : Test k) (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) : Bool :=
  match test with
  | .constant b => b
  | .equal x y => decide (v x = v y)
  | .literal c x j sign =>
      let l := CNFLookup.selected F (v c).val j
      decide (l.1 = (v x).val ∧ l.2 = sign)

variable {K Aux : Type} [DecidableEq K]

def normalize : EvalProgram K Aux := .atom (.load (fun s => (((s.1.1.1, true), s.1.2), none)))
def saveSign (sign : Bool) : EvalProgram K Aux :=
  .atom (.load (fun s => (((s.1.1.1, decide (s.1.2 = sign)), false), none)))
def finishLiteral : EvalProgram K Aux :=
  .atom (.load (fun s => (((s.1.1.1, true), s.1.1.2 && s.1.2), none)))

def compile {k : ℕ} (test : Test k) (input : Inputs K k) (work : Work → K) : EvalProgram K Aux :=
  match test with
  | .constant b => answer b
  | .equal x y =>
      .seq (StackCopy.copy (input.coordinate x) (work .index) (work .tmp))
        (.seq (StackCopy.copy (input.coordinate y) (work .compare) (work .tmp))
          (.seq (StackEqual.equal (work .index) (work .compare)) normalize))
  | .literal c x j sign =>
      .seq (StackCopy.copy input.word (work .cursor) (work .tmp))
        (.seq (StackCopy.copy (input.coordinate c) (work .counter) (work .tmp))
          (.seq (StackCopy.copy (input.coordinate x) (work .compare) (work .tmp))
            (.seq (answer (CNFLiteral.defaultLiteral j).2)
              (.seq (CNFLookup.program (work .counter) (work .cursor) (work .index) j)
                (.seq (saveSign sign)
                  (.seq (StackEqual.equal (work .index) (work .compare))
                    (.seq (StackClear.clear (work .cursor)) finishLiteral)))))))

noncomputable def cost : Polynomial ℕ := 2 * Polynomial.X ^ 2 + 60 * Polynomial.X + 100

def copied (src dst : K) (s : EvalStore K Aux) : EvalStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk dst (s.stk src ++ s.stk dst)⟩

theorem correct_equal {k : ℕ} (input : Inputs K k) (work : Work → K)
    (hi : Function.Injective work) (hf : ∀ w, input.Fresh (work w))
    (F : ShortCNF.Formula) (v : Fin k → Fin (ShortCNF.encode F).length) (s : EvalStore K Aux)
    (hc : Clean work s) (hr : Represents input F v s) (x y : Fin k) :
    ∃ c, c ≤ cost.eval (ShortCNF.encode F).length ∧
      Returns (compile (.equal x y) input work) s (value (.equal x y) F v) c := by
  change ∀ w, s.stk (work w) = [] at hc
  have hne (i j : Work) (h : i ≠ j) : work i ≠ work j := fun he => h (hi he)
  have hcoord (w : Work) (i : Fin k) : input.coordinate i ≠ work w := Ne.symm ((hf w).2.2 i)
  let s₁ := copied (input.coordinate x) (work .index) s
  let s₂ := copied (input.coordinate y) (work .compare) s₁
  have hp := StackCopy.copy_store (input.coordinate x) (work .index) (work .tmp)
    (hcoord _ _) (hcoord _ _) (hne _ _ (by decide)) s (hc _)
  have htmp : s₁.stk (work .tmp) = [] := by simp [s₁, copied, hne, hc]
  have hq := StackCopy.copy_store (input.coordinate y) (work .compare) (work .tmp)
    (hcoord _ _) (hcoord _ _) (hne _ _ (by decide)) s₁ htmp
  have hx : (s₂.stk (work .index)).length = (v x).val := by
    simp [s₂, s₁, copied, hne, hc, hr.2.2]
  have hy : (s₂.stk (work .compare)).length = (v y).val := by
    simp [s₂, s₁, copied, hne, hcoord, hc, hr.2.2]
  obtain ⟨c, hcBound, he⟩ := StackEqual.equal_store (work .index) (work .compare)
    (hne _ _ (by decide)) s₂
  let s₃ : EvalStore K Aux :=
    ⟨((s₂.state.1.1, decide ((s₂.stk (work .index)).length = (s₂.stk (work .compare)).length)), none),
      Function.update (Function.update s₂.stk (work .index) []) (work .compare) []⟩
  have hn := Executes.atom
    (.load (fun q : ((Aux × Bool) × Bool) × Option Bool => (((q.1.1.1, true), q.1.2), none))) s₃
  have hend : Op.apply
      (.load (fun q : ((Aux × Bool) × Bool) × Option Bool => (((q.1.1.1, true), q.1.2), none))) s₃ =
      result (decide (v x = v y)) s := by
    apply Store.ext
    · simp only [Op.apply, s₃, hx, hy, result]
      simp [s₂, s₁, copied, Fin.ext_iff]
    · funext key
      by_cases hidx : key = work .index
      · subst key; simp [s₃, s₂, s₁, copied, Op.apply, result, hne, hc]
      · by_cases hcmp : key = work .compare
        · subst key; simp [s₃, s₂, s₁, copied, Op.apply, result, hc]
        · simp [s₃, s₂, s₁, copied, Op.apply, result, hidx, hcmp]
  rw [hend] at hn
  have h := Executes.seq hp (Executes.seq hq (Executes.seq he hn))
  refine ⟨_, ?_, h⟩
  rw [hx, hy] at hcBound
  have hlenx : (s.stk (input.coordinate x)).length = (v x).val := by simp [hr.2.2]
  have hleny : (s₁.stk (input.coordinate y)).length = (v y).val := by
    simp [s₁, copied, hcoord, hr.2.2]
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hlenx, hleny]
  have hvx := (v x).isLt
  have hvy := (v y).isLt
  omega

end Lax762056Proofs.CNFAtom
