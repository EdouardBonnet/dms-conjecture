import Lax222097Proofs.CNFWriter

set_option backward.isDefEq.respectTransparency false

namespace Lax222097Proofs.CNFWriter

open Lax222097Proofs.QueryCompiler StackProgram StackBoolean
open QueryProgram (LoopWork written payload written_pack payload_start fold_prepend_reverse)

variable {K Aux : Type} [DecidableEq K]

theorem correct_forEach {k : ℕ} {p : Query (k + 1)}
    (hp : Correct (K := K) (Aux := Aux) p) : Correct (K := K) (Aux := Aux) (.forEach p) := by
  intro input out work hs ho hi hf hw F v s hc hr
  let base := payload out s
  let input' := input.existsPorts (work .coordinate)
  let child := work ∘ LoopWork.child
  let bits : ℕ → List Bool := fun i => if hi : i < (ShortCNF.encode F).length then word p F (Fin.cons ⟨i, hi⟩ v) else []
  let f : ℕ → List Bool → List Bool := fun i acc => (bits i).reverse ++ acc
  have hprivate : [work .counter, work .coordinate, work .tmp].Nodup :=
    (List.nodup_map_iff hi).mpr (by simp :
      ([.counter, .coordinate, .tmp] : List (LoopWork (Work p))).Nodup)
  have hsep : [input.domain, work .counter, work .coordinate, work .tmp].Nodup := by
    simpa [List.nodup_cons, Ne.symm (hf .counter).1, Ne.symm (hf .coordinate).1,
      Ne.symm (hf .tmp).1] using hprivate
  have hbc : ∀ acc, (base acc).stk (work .counter) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using! hc .counter
  have hbd : ∀ acc, (base acc).stk (work .coordinate) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using! hc .coordinate
  have hbt : ∀ acc, (base acc).stk (work .tmp) = [] := by
    intro acc
    simpa [base, payload, StackTuples.setStack, result, hw] using! hc .tmp
  have hbody : ∀ i, i < (ShortCNF.encode F).length → ∀ acc rem scratch,
      ∃ c scratch', c ≤ (cost p).eval (ShortCNF.encode F).length ∧
        Executes (compile p input' out child)
          (StackFor.pack base (work .counter) (work .coordinate) acc i rem scratch)
          (StackFor.pack base (work .counter) (work .coordinate) (f i acc) i rem scratch') c := by
    intro i hia acc rem scratch
    have hrbase : FormulaProgram.Represents input (CNFSource.source F) v (QueryProgram.emptyEnv (ShortCNF.encode F).length) (base acc) :=
      (hr.result false).setStack ho acc
    have hrpack := hrbase.pack base (work .counter) (work .coordinate)
      (hf .counter) (hf .coordinate) acc i rem scratch
    have hrchild : FormulaProgram.Represents input' (CNFSource.source F) (Fin.cons ⟨i, hia⟩ v) (QueryProgram.emptyEnv (ShortCNF.encode F).length)
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
      (fun w => hw (.child w)) F (Fin.cons ⟨i, hia⟩ v) _ hcleanpack hrchild
    rw [written_pack out _ _ (Ne.symm (hw .counter)) (Ne.symm (hw .coordinate))] at hrun
    exact ⟨c, none, hb, by simpa [base, bits, f, hia] using! hrun⟩
  obtain ⟨c, hb, hrun⟩ := StackFor.forValues_executes base input.domain (work .counter)
    (work .coordinate) (work .tmp) hsep (compile p input' out child) f (ShortCNF.encode F).length
    ((cost p).eval (ShortCNF.encode F).length) hbc hbd hbt hbody (s.stk out)
    (by simpa [base, payload, StackTuples.setStack, result, Ne.symm ho.1] using! hr.domain)
  have hbits : (List.range (ShortCNF.encode F).length).flatMap bits = word (.forEach p) F v := by
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    change (List.finRange (ShortCNF.encode F).length).flatMap (fun x => bits x.val) = _
    congr 1
    funext x
    simp [bits]
  have hfold : StackFor.foldRange f 0 (ShortCNF.encode F).length (s.stk out) =
      (word (.forEach p) F v).reverse ++ s.stk out := by
    rw [StackFor.foldRange_zero_eq]
    change (List.range (ShortCNF.encode F).length).foldl (fun acc i => (bits i).reverse ++ acc) (s.stk out) = _
    rw [fold_prepend_reverse, hbits]
  have hfinish : StackFor.reset (base (StackFor.foldRange f 0 (ShortCNF.encode F).length (s.stk out))) =
      written out (word (.forEach p) F v) s := by
    rw [hfold]
    rfl
  rw [hfinish, show base (s.stk out) = result false s from payload_start out s] at hrun
  refine ⟨1 + c, ?_, ?_⟩
  · simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · exact Executes.seq (answer_returns false s) hrun

theorem compile_correct {k : ℕ} (q : Query k) : Correct (K := K) (Aux := Aux) q := by
  induction q with
  | emit test => exact correct_emit test
  | seq p q hp hq => exact correct_seq hp hq
  | forEach p hp => exact correct_forEach hp

end Lax222097Proofs.CNFWriter
