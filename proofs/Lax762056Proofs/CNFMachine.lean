import Lax762056Proofs.CNFWriterLoop
import Lax762056Proofs.QueryBounds

namespace Lax762056Proofs.CNFMachine

open Lax762056Proofs.QueryCompiler StackProgram StackBoolean

abbrev Q := CNFWriter.Query 0

inductive Port (q : Q)
  | input | output | acc | domain | count | tmp
  | query (w : CNFWriter.Work q)
  deriving DecidableEq, Fintype

def initial : ((Unit × Bool) × Bool) × Option Bool := ((((), true), false), none)

def inputs (q : Q) : FormulaProgram.Inputs (Port q) [1] 0 [] where
  domain := .domain
  element := Fin.elim0
  symbol := fun _ => .input
  relation := fun r => Fin.elim0 r

def prepare (q : Q) : EvalProgram (Port q) Unit :=
  .seq (StackCopy.copy .input .count .tmp) (StackCount.count .count .domain)

def finish (q : Q) : EvalProgram (Port q) Unit :=
  .seq (StackClear.clear .input)
    (.seq (StackClear.clear .domain) (.seq (StackTransfer.transfer .acc .output) (answer false)))

def program (q : Q) : EvalProgram (Port q) Unit :=
  .seq (prepare q) (.seq (CNFWriter.compile q (inputs q) .acc Port.query) (finish q))

def prepared (q : Q) (F : ShortCNF.Formula) : EvalStore (Port q) Unit :=
  ⟨initial, fun p => match p with
    | .input => ShortCNF.encode F
    | .domain => List.replicate (ShortCNF.encode F).length true
    | _ => []⟩

theorem prepare_executes (q : Q) (F : ShortCNF.Formula) :
    ∃ c, c ≤ 10 * (ShortCNF.encode F).length + 6 ∧
      Executes (prepare q) (ioStore .input initial (ShortCNF.encode F)) (prepared q F) c := by
  let s₀ : EvalStore (Port q) Unit := ioStore .input initial (ShortCNF.encode F)
  let s₁ := CNFAtom.copied (Port.input : Port q) .count s₀
  have hcopy := StackCopy.copy_store (Port.input : Port q) .count .tmp
    (by simp) (by simp) (by simp) s₀ (by simp [s₀, ioStore])
  obtain ⟨c, hc, hcount⟩ := StackCount.count_executes s₀.stk (Port.count : Port q) .domain
    (by simp) (ShortCNF.encode F) [] initial.1 none
  have hin : StackTransfer.working s₀.stk (Port.count : Port q) .domain
      (ShortCNF.encode F) [] initial.1 none = s₁ := by
    apply Store.ext
    · rfl
    · funext p
      cases p <;> simp [StackTransfer.working, s₁, s₀, CNFAtom.copied, ioStore]
  have hout : StackTransfer.working s₀.stk (Port.count : Port q) .domain []
      (List.replicate (ShortCNF.encode F).length true ++ []) initial.1 none = prepared q F := by
    apply Store.ext
    · rfl
    · funext p
      cases p <;> simp [StackTransfer.working, s₀, ioStore, prepared]
  rw [hin, hout] at hcount
  have h := Executes.seq hcopy hcount
  refine ⟨_, ?_, h⟩
  have hlen : (s₀.stk .input).length = (ShortCNF.encode F).length := by simp [s₀, ioStore]
  rw [hlen]
  omega

theorem finish_executes (q : Q) (F : ShortCNF.Formula) (bits : List Bool) :
    Executes (finish q) (QueryProgram.written (Port.acc : Port q) bits (prepared q F))
      (ioStore .output initial bits) (3 * bits.length + 4 * (ShortCNF.encode F).length + 7) := by
  let s₀ := QueryProgram.written (Port.acc : Port q) bits (prepared q F)
  let s₁ : EvalStore (Port q) Unit := ⟨(s₀.state.1, none), Function.update s₀.stk .input []⟩
  let s₂ : EvalStore (Port q) Unit := ⟨(s₁.state.1, none), Function.update s₁.stk .domain []⟩
  let s₃ : EvalStore (Port q) Unit := ⟨(s₂.state.1, none),
    Function.update (Function.update s₂.stk .acc []) .output
      ((s₂.stk .acc).reverse ++ s₂.stk .output)⟩
  have h₁ := StackClear.clear_store (Port.input : Port q) s₀
  have h₂ := StackClear.clear_store (Port.domain : Port q) s₁
  have h₃ := StackTransfer.transfer_store (Port.acc : Port q) .output (by simp) s₂
  have h₄ := answer_returns false s₃
  have h := Executes.seq h₁ (Executes.seq h₂ (Executes.seq h₃ h₄))
  have hl₀ : (s₀.stk .input).length = (ShortCNF.encode F).length := by
    simp [s₀, QueryProgram.written, StackTuples.setStack, result, prepared]
  have hl₁ : (s₁.stk .domain).length = (ShortCNF.encode F).length := by
    simp [s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared]
  have hl₂ : (s₂.stk .acc).length = bits.length := by
    simp [s₂, s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared]
  have hend : result false s₃ = ioStore (Port.output : Port q) initial bits := by
    apply Store.ext
    · rfl
    · funext p
      cases p <;> simp [s₃, s₂, s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared, ioStore]
  change Executes (finish q) s₀ (result false s₃)
    ((2 * (s₀.stk .input).length + 2) + ((2 * (s₁.stk .domain).length + 2) +
      ((3 * (s₂.stk .acc).length + 2) + 1))) at h
  rw [hl₀, hl₁, hl₂, hend] at h
  convert h using 1 <;> omega

noncomputable def time (q : Q) : Polynomial ℕ := 4 * CNFWriter.cost q + 14 * Polynomial.X + 20

theorem program_executes (q : Q) (F : ShortCNF.Formula) :
    ∃ c, c ≤ (time q).eval (ShortCNF.encode F).length ∧
      Executes (program q) (ioStore .input initial (ShortCNF.encode F))
        (ioStore .output initial (CNFWriter.word q F Fin.elim0)) c := by
  obtain ⟨a, ha, hp⟩ := prepare_executes q F
  have hs : (inputs q).Safe := ⟨fun _ => by simp [inputs], fun r => Fin.elim0 r⟩
  have ho : (inputs q).Fresh .acc :=
    ⟨by simp [inputs], fun r => Fin.elim0 r, fun _ => by simp [inputs], fun r => Fin.elim0 r⟩
  have hf : ∀ w, (inputs q).Fresh (Port.query w) := fun w =>
    ⟨by simp [inputs], fun r => Fin.elim0 r, fun _ => by simp [inputs], fun r => Fin.elim0 r⟩
  have hr : FormulaProgram.Represents (inputs q) (CNFSource.source F) Fin.elim0
      (QueryProgram.emptyEnv (ShortCNF.encode F).length) (prepared q F) := by
    constructor
    · rfl
    · exact fun r => Fin.elim0 r
    · intro r; exact (CNFSource.source_table F r).symm
    · exact fun r => Fin.elim0 r
  obtain ⟨b, hb, hquery⟩ := CNFWriter.compile_correct q (inputs q) .acc Port.query hs ho
    (fun _ _ h => Port.query.inj h) hf (fun _ => by simp) F Fin.elim0 (prepared q F)
    (fun _ => rfl) hr
  let bits := CNFWriter.word q F Fin.elim0
  have hl := QueryProgram.execution_length hquery (Port.acc : Port q)
  have hlen : bits.length ≤ b := by
    simpa [bits, QueryProgram.written, StackTuples.setStack, result, prepared] using hl
  have hfinish := finish_executes q F bits
  refine ⟨_, ?_, Executes.seq hp (Executes.seq hquery hfinish)⟩
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- Every fixed query built from CNF literal lookups and bounded position
loops is computed by a single finite machine with a polynomial time bound. -/
theorem polynomial_time (q : Q) :
    Nonempty (Turing.TM2ComputableInPolyTime ShortCNF.encode id (fun F => CNFWriter.word q F Fin.elim0)) :=
  program_polytime (program q) .input .output initial ShortCNF.encode id
    (fun F => CNFWriter.word q F Fin.elim0) (time q) (program_executes q)

end Lax762056Proofs.CNFMachine
