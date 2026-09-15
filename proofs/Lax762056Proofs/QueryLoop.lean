import Lax762056Proofs.QueryProgram

namespace Lax762056Proofs.QueryProgram

open Lax762056Proofs.QueryDefinitions.OrderedStructures Lax762056Proofs.QueryDefinitions.FixedPointSyntax
open Lax762056Proofs.QueryCompiler StackProgram StackBoolean

variable {K Aux : Type} [DecidableEq K]

def payload (out : K) (s : EvalStore K Aux) (bits : List Bool) : EvalStore K Aux :=
  StackTuples.setStack (result false s) out bits

theorem payload_start (out : K) (s : EvalStore K Aux) : payload out s (s.stk out) = result false s := by
  simp [payload, StackTuples.setStack, result]

theorem written_pack (out counter coordinate : K) (hc : out ≠ counter) (hd : out ≠ coordinate)
    (s : EvalStore K Aux) (acc bits : List Bool) (i rem : ℕ) (scratch : Option Bool) :
    written out bits (StackFor.pack (payload out s) counter coordinate acc i rem scratch) =
      StackFor.pack (payload out s) counter coordinate (bits.reverse ++ acc) i rem none := by
  apply Store.ext
  · rfl
  · funext key
    by_cases ho : key = out
    · subst key
      simp [written, payload, StackFor.pack, StackTransfer.working, StackTuples.setStack, result, hc, hd]
    · by_cases hct : key = counter <;> by_cases hcd : key = coordinate <;>
        simp_all [written, payload, StackFor.pack, StackTransfer.working, StackTuples.setStack, result]

theorem fold_prepend_reverse {α : Type} (f : α → List Bool) (xs : List α) (acc : List Bool) :
    xs.foldl (fun a x => (f x).reverse ++ a) acc = (xs.flatMap f).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.reverse_append, List.append_assoc]

theorem correct_forEach {σ : Vocabulary} {k : ℕ} {p : Query σ (k + 1)}
    (hp : Correct (K := K) (Aux := Aux) p) : Correct (K := K) (Aux := Aux) (.forEach p) := by
  intro input out work hs ho hi hf hw A v s hc hr
  let base := payload out s
  let input' := input.existsPorts (work .coordinate)
  let child := work ∘ LoopWork.child
  let bits : ℕ → List Bool := fun i => if hi : i < A.size then word p A (Fin.cons ⟨i, hi⟩ v) else []
  let f : ℕ → List Bool → List Bool := fun i acc => (bits i).reverse ++ acc
  have hprivate : [work .counter, work .coordinate, work .tmp].Nodup :=
    (List.nodup_map_iff hi).mpr (by simp :
      ([.counter, .coordinate, .tmp] : List (LoopWork (Work p))).Nodup)
  have hsep : [input.domain, work .counter, work .coordinate, work .tmp].Nodup := by
    simpa [List.nodup_cons, Ne.symm (hf .counter).1, Ne.symm (hf .coordinate).1,
      Ne.symm (hf .tmp).1] using hprivate
  have hbc : ∀ acc, (base acc).stk (work .counter) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using hc .counter
  have hbd : ∀ acc, (base acc).stk (work .coordinate) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using hc .coordinate
  have hbt : ∀ acc, (base acc).stk (work .tmp) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using hc .tmp
  have hbody : ∀ i, i < A.size → ∀ acc rem scratch,
      ∃ c scratch', c ≤ (cost p).eval A.size ∧
        Executes (compile p input' out child)
          (StackFor.pack base (work .counter) (work .coordinate) acc i rem scratch)
          (StackFor.pack base (work .counter) (work .coordinate) (f i acc) i rem scratch') c := by
    intro i hia acc rem scratch
    have hrbase : FormulaProgram.Represents input A v (emptyEnv A.size) (base acc) :=
      (hr.result false).setStack ho acc
    have hrpack := hrbase.pack base (work .counter) (work .coordinate)
      (hf .counter) (hf .coordinate) acc i rem scratch
    have hrchild : FormulaProgram.Represents input' A (Fin.cons ⟨i, hia⟩ v) (emptyEnv A.size)
        (StackFor.pack base (work .counter) (work .coordinate) acc i rem scratch) :=
      hrpack.existsPorts _ ⟨i, hia⟩ (by simp [StackFor.pack, StackTransfer.working])
    have hclean : FormulaProgram.Clean child (base acc) :=
      (FormulaProgram.Clean.result (fun w => hc (.child w)) false).setStack out
        (fun w => hw (.child w)) acc
    have hcleanpack := hclean.pack base (work .counter) (work .coordinate)
      (by intro w h; have he := hi h; cases he)
      (by intro w h; have he := hi h; cases he) acc i rem scratch
    obtain ⟨c, hb, hrun⟩ := hp input' out child (hs.existsPorts _)
      (ho.existsPorts (Ne.symm (hw .coordinate)))
      (fun _ _ h => LoopWork.child.inj (hi h))
      (fun w => (hf (.child w)).existsPorts (by intro h; have he := hi h; cases he))
      (fun w => hw (.child w)) A (Fin.cons ⟨i, hia⟩ v) _ hcleanpack hrchild
    rw [written_pack out _ _ (Ne.symm (hw .counter)) (Ne.symm (hw .coordinate))] at hrun
    exact ⟨c, none, hb, by simpa [base, bits, f, hia] using hrun⟩
  obtain ⟨c, hb, hrun⟩ := StackFor.forValues_executes base input.domain (work .counter)
    (work .coordinate) (work .tmp) hsep (compile p input' out child) f A.size
    ((cost p).eval A.size) hbc hbd hbt hbody (s.stk out)
    (by simpa [base, payload, StackTuples.setStack, result, Ne.symm ho.1] using hr.domain)
  have hbits : (List.range A.size).flatMap bits = word (.forEach p) A v := by
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    change (List.finRange A.size).flatMap (fun x => bits x.val) = _
    congr 1
    funext x
    simp [bits]
  have hfold : StackFor.foldRange f 0 A.size (s.stk out) =
      (word (.forEach p) A v).reverse ++ s.stk out := by
    rw [StackFor.foldRange_zero_eq]
    change (List.range A.size).foldl (fun acc i => (bits i).reverse ++ acc) (s.stk out) = _
    rw [fold_prepend_reverse, hbits]
  have hfinish : StackFor.reset (base (StackFor.foldRange f 0 A.size (s.stk out))) =
      written out (word (.forEach p) A v) s := by
    rw [hfold]
    rfl
  rw [hfinish, show base (s.stk out) = result false s from payload_start out s] at hrun
  refine ⟨1 + c, ?_, ?_⟩
  · simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · exact Executes.seq (answer_returns false s) hrun

theorem compile_correct {σ : Vocabulary} {k : ℕ} (q : Query σ k) :
    Correct (K := K) (Aux := Aux) q := by
  induction q with
  | emit φ ψ => exact correct_emit φ ψ
  | seq p q hp hq => exact correct_seq hp hq
  | forEach p hp => exact correct_forEach hp

end Lax762056Proofs.QueryProgram
