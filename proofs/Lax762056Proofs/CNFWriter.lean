import Lax762056Proofs.CNFSource

namespace Lax762056Proofs.CNFWriter

open Lax979537Proofs StackProgram StackBoolean
open QueryProgram (LoopWork written written_clean written_represents written_append)

inductive Query : ℕ → Type
  | emit {k : ℕ} (test : CNFAtom.Test k) : Query k
  | seq {k : ℕ} (p q : Query k) : Query k
  | forEach {k : ℕ} (p : Query (k + 1)) : Query k

@[reducible] def Work : {k : ℕ} → Query k → Type
  | _, .emit _ => CNFAtom.Work
  | _, .seq p q => Work p ⊕ Work q
  | _, .forEach p => LoopWork (Work p)

instance workFintype {k : ℕ} (q : Query k) : Fintype (Work q) :=
  match q with
  | .emit _ => inferInstanceAs (Fintype CNFAtom.Work)
  | .seq p q =>
    letI := workFintype p
    letI := workFintype q
    inferInstanceAs (Fintype (Work p ⊕ Work q))
  | .forEach p =>
    letI := workFintype p
    inferInstanceAs (Fintype (LoopWork (Work p)))

instance workDecidableEq {k : ℕ} (q : Query k) : DecidableEq (Work q) :=
  match q with
  | .emit _ => inferInstanceAs (DecidableEq CNFAtom.Work)
  | .seq p q =>
    letI := workDecidableEq p
    letI := workDecidableEq q
    inferInstanceAs (DecidableEq (Work p ⊕ Work q))
  | .forEach p =>
    letI := workDecidableEq p
    inferInstanceAs (DecidableEq (LoopWork (Work p)))

def word : {k : ℕ} → Query k → (F : ShortCNF.Formula) →
    (Fin k → Fin (ShortCNF.encode F).length) → List Bool
  | _, .emit test, F, v => [CNFAtom.value test F v]
  | _, .seq p q, F, v => word p F v ++ word q F v
  | _, .forEach p, F, v => (List.finRange (ShortCNF.encode F).length).flatMap (fun x => word p F (Fin.cons x v))

noncomputable def cost : {k : ℕ} → Query k → Polynomial ℕ
  | _, .emit _ => CNFAtom.cost + 2
  | _, .seq p q => cost p + cost q
  | _, .forEach p => (cost p + 12) * Polynomial.X + 9

variable {K Aux : Type} [DecidableEq K]

def compile : {k : ℕ} → (q : Query k) → FormulaProgram.Inputs K [1] k [] →
    K → (Work q → K) → EvalProgram K Aux
  | _, .emit test, input, out, work =>
    .seq (CNFAtom.compile test (CNFSource.ports input) work)
      (.seq (QueryProgram.writeBit out) (answer false))
  | _, .seq p q, input, out, work =>
    .seq (compile p input out (work ∘ Sum.inl)) (compile q input out (work ∘ Sum.inr))
  | _, .forEach p, input, out, work =>
    .seq (answer false)
      (StackFor.forValues input.domain (work .counter) (work .coordinate) (work .tmp)
        (compile p (input.existsPorts (work .coordinate)) out (work ∘ LoopWork.child)))

def Correct {k : ℕ} (q : Query k) : Prop :=
  ∀ (input : FormulaProgram.Inputs K [1] k []) (out : K) (work : Work q → K),
    input.Safe → input.Fresh out → Function.Injective work →
    (∀ w, input.Fresh (work w)) → (∀ w, work w ≠ out) →
    ∀ (F : ShortCNF.Formula) (v : Fin k → Fin (ShortCNF.encode F).length) (s : EvalStore K Aux),
      FormulaProgram.Clean work s →
      FormulaProgram.Represents input (CNFSource.source F) v
        (QueryProgram.emptyEnv (ShortCNF.encode F).length) s →
      ∃ c, c ≤ (cost q).eval (ShortCNF.encode F).length ∧
        Executes (compile q input out work) s (written out (word q F v) s) c

theorem correct_emit {k : ℕ} (test : CNFAtom.Test k) :
    Correct (K := K) (Aux := Aux) (.emit test) := by
  intro input out work _ _ hi hf _ F v s hc hr
  obtain ⟨c, hBound, htest⟩ := CNFAtom.compile_correct test (CNFSource.ports input) work hi
    (fun w => CNFSource.fresh (hf w)) F v s hc (CNFSource.represents hr)
  have hp := Executes.atom (.push out (fun q : ((Aux × Bool) × Bool) × Option Bool => q.1.2))
    (result (CNFAtom.value test F v) s)
  have hr := answer_returns false
    (Op.apply (.push out (fun q : ((Aux × Bool) × Bool) × Option Bool => q.1.2))
      (result (CNFAtom.value test F v) s))
  refine ⟨c + 2, ?_, ?_⟩
  · simpa [cost] using Nat.add_le_add_right hBound 2
  · simpa [compile, word, QueryProgram.writeBit, written, StackTuples.setStack,
      result, Returns, Op.apply] using Executes.seq htest (Executes.seq hp hr)

theorem correct_seq {k : ℕ} {p q : Query k}
    (hp : Correct (K := K) (Aux := Aux) p) (hq : Correct (K := K) (Aux := Aux) q) :
    Correct (K := K) (Aux := Aux) (.seq p q) := by
  intro input out work hs ho hi hf hw F v s hc hr
  obtain ⟨a, ha, hp⟩ := hp input out (work ∘ Sum.inl) hs ho
    (fun _ _ h => Sum.inl.inj (hi h)) (fun w => hf (.inl w)) (fun w => hw (.inl w))
    F v s (fun w => hc (.inl w)) hr
  obtain ⟨b, hb, hq⟩ := hq input out (work ∘ Sum.inr) hs ho
    (fun _ _ h => Sum.inr.inj (hi h)) (fun w => hf (.inr w)) (fun w => hw (.inr w))
    F v (written out (word p F v) s)
    (written_clean (fun w => hc (.inr w)) (fun w => hw (.inr w)) _)
    (written_represents hr ho _)
  refine ⟨a + b, ?_, ?_⟩
  · simpa [cost] using Nat.add_le_add ha hb
  · simpa only [compile, word, written_append] using Executes.seq hp hq

end Lax762056Proofs.CNFWriter
