import Lax762056Proofs.GraphQuery

namespace Lax762056Proofs.GraphQuery

open Lax762056 GraphEncoding Lax979537.OrderedStructures
open Lax979537Proofs StackProgram StackBoolean

theorem finish_executes (q : Q) (I : Instance) (bits : List Bool) :
    Executes (finish q) (QueryProgram.written (Port.acc : Port q) bits (prepared q I))
      (ioStore .output initial (bits ++ unary I.threshold))
      (3 * bits.length + 6 * I.threshold + 2 * I.order ^ 2 + 2 * I.order + 15) := by
  let s₀ := QueryProgram.written (Port.acc : Port q) bits (prepared q I)
  let s₁ : EvalStore (Port q) Unit := ⟨(s₀.state.1, none),
    Function.update (Function.update s₀.stk .input []) .acc
      ((s₀.stk .input).reverse ++ s₀.stk .acc)⟩
  let s₂ : EvalStore (Port q) Unit := ⟨(s₁.state.1, none), Function.update s₁.stk .domain []⟩
  let s₃ : EvalStore (Port q) Unit := ⟨(s₂.state.1, none), Function.update s₂.stk .table []⟩
  let s₄ : EvalStore (Port q) Unit := ⟨(s₃.state.1, none),
    Function.update (Function.update s₃.stk .acc []) .output
      ((s₃.stk .acc).reverse ++ s₃.stk .output)⟩
  have h₁ := StackTransfer.transfer_store (Port.input : Port q) .acc (by simp [inputs]) s₀
  have h₂ := StackClear.clear_store (Port.domain : Port q) s₁
  have h₃ := StackClear.clear_store (Port.table : Port q) s₂
  have h₄ := StackTransfer.transfer_store (Port.acc : Port q) .output (by simp [inputs]) s₃
  have h₅ := answer_returns false s₄
  have h := Executes.seq h₁ (Executes.seq h₂ (Executes.seq h₃ (Executes.seq h₄ h₅)))
  have hl₀ : (s₀.stk .input).length = I.threshold + 1 := by
    simp [s₀, QueryProgram.written, StackTuples.setStack, result, prepared, unary]
  have hl₁ : (s₁.stk .domain).length = I.order := by
    simp [s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared]
  have hl₂ : (s₂.stk .table).length = I.order ^ 2 := by
    simp [s₂, s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared, matrix_length]
  have hl₃ : (s₃.stk .acc).length = bits.length + I.threshold + 1 := by
    simp [s₃, s₂, s₁, s₀, QueryProgram.written, StackTuples.setStack, result, prepared, unary]
    omega
  have hend : result false s₄ = ioStore (Port.output : Port q) initial (bits ++ unary I.threshold) := by
    apply Store.ext
    · rfl
    · funext k
      cases k <;>
        simp [s₄, s₃, s₂, s₁, s₀, QueryProgram.written, StackTuples.setStack, result,
          prepared, ioStore, initial, List.reverse_append]
  change Executes (finish q) s₀ (result false s₄)
    ((3 * (s₀.stk .input).length + 2) + ((2 * (s₁.stk .domain).length + 2) +
      ((2 * (s₂.stk .table).length + 2) + ((3 * (s₃.stk .acc).length + 2) + 1)))) at h
  rw [hl₀, hl₁, hl₂, hl₃, hend] at h
  convert h using 1 <;> omega

theorem prepared_represents (q : Q) (I : Instance) :
    FormulaProgram.Represents (inputs q) (source I.graph) Fin.elim0
      (QueryProgram.emptyEnv I.order) (prepared q I) := by
  constructor
  · rfl
  · exact fun r => Fin.elim0 r
  · intro r
    exact (source_table I.graph r).symm
  · exact fun r => Fin.elim0 r

theorem program_executes (q : Q) (I : Instance) :
    ∃ t, t ≤ (time q).eval (encode I).length ∧
      Executes (program q) (ioStore .input initial (encode I))
        (ioStore .output initial (render q I)) t := by
  have hparse := parse_executes q I
  obtain ⟨c, hc, hread⟩ := readMatrix_executes q I
  have hs : (inputs q).Safe := by
    refine ⟨fun _ => by simp [inputs], (fun r => Fin.elim0 r)⟩
  have ho : (inputs q).Fresh .acc := by
    refine ⟨by simp [inputs], (fun r => Fin.elim0 r), fun _ => by simp [inputs], (fun r => Fin.elim0 r)⟩
  have hf : ∀ w, (inputs q).Fresh (Port.query w) := by
    intro w
    refine ⟨by simp [inputs], (fun r => Fin.elim0 r), fun _ => by simp [inputs], (fun r => Fin.elim0 r)⟩
  obtain ⟨d, hd, hquery⟩ := QueryProgram.compile_correct q (inputs q) .acc Port.query hs ho
    (fun _ _ h => Port.query.inj h) hf (fun _ => by simp) (source I.graph) Fin.elim0
    (prepared q I) (fun _ => rfl) (prepared_represents q I)
  let bits := QueryProgram.word q (source I.graph) Fin.elim0
  have hlen := QueryProgram.execution_length hquery (Port.acc : Port q)
  have hbits : bits.length ≤ d := by
    simpa [bits, QueryProgram.written, StackTuples.setStack, result, prepared] using hlen
  have hfinish := finish_executes q I bits
  have h := Executes.seq hparse (Executes.seq hread (Executes.seq hquery hfinish))
  refine ⟨(3 * I.order + 2) + (c + (d +
    (3 * bits.length + 6 * I.threshold + 2 * I.order ^ 2 + 2 * I.order + 15))), ?_, h⟩
  have hn : I.order ≤ (encode I).length := by rw [EncodingFacts.encode_length]; omega
  have hk : I.threshold ≤ (encode I).length := by rw [EncodingFacts.encode_length]; omega
  have hc' := PolynomialComposition.eval_mono (StackReadTable.costPolynomial 2) hn
  have hd' := PolynomialComposition.eval_mono (QueryProgram.cost q) hn
  have hn₂ := Nat.pow_le_pow_left hn 2
  change d ≤ (QueryProgram.cost q).eval I.order at hd
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- Any fixed bounded query on the input graph can output its bits followed
by the original unary threshold, in the archive's exact polynomial-time model. -/
theorem polynomial_time (q : Q) :
    Nonempty (Turing.TM2ComputableInPolyTime encode id (render q)) :=
  program_polytime (program q) .input .output initial encode id (render q) (time q) (program_executes q)

end Lax762056Proofs.GraphQuery
