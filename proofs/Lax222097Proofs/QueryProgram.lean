import Lax222097Proofs.QueryCompiler.FormulaLfpCorrectness
import Lax222097Proofs.QueryCompiler.StackFor

/-! A finite stack-program compiler for bounded tuple enumeration with
first-order tests and binary output. The graph construction can enumerate
vertices and adjacency bits without storing an input-dependent program. -/

namespace Lax222097Proofs.QueryProgram

open Lax222097Proofs.QueryDefinitions.OrderedStructures Lax222097Proofs.QueryDefinitions.FixedPointSyntax
open Lax222097Proofs.QueryCompiler StackProgram StackBoolean

inductive Query (σ : Vocabulary) : ℕ → Type
  | emit {k : ℕ} (test bit : RawFormula σ k []) : Query σ k
  | seq {k : ℕ} (p q : Query σ k) : Query σ k
  | forEach {k : ℕ} (p : Query σ (k + 1)) : Query σ k

inductive LoopWork (W : Type)
  | counter | coordinate | tmp
  | child (w : W)
  deriving DecidableEq, Fintype

@[reducible] def Work {σ : Vocabulary} : {k : ℕ} → Query σ k → Type
  | _, .emit φ ψ => FormulaProgram.Work φ ⊕ FormulaProgram.Work ψ
  | _, .seq p q => Work p ⊕ Work q
  | _, .forEach p => LoopWork (Work p)

instance workFintype {σ : Vocabulary} {k : ℕ} (q : Query σ k) : Fintype (Work q) :=
  match q with
  | .emit φ ψ => inferInstanceAs (Fintype (FormulaProgram.Work φ ⊕ FormulaProgram.Work ψ))
  | .seq p q =>
      letI := workFintype p
      letI := workFintype q
      inferInstanceAs (Fintype (Work p ⊕ Work q))
  | .forEach p =>
      letI := workFintype p
      inferInstanceAs (Fintype (LoopWork (Work p)))

instance workDecidableEq {σ : Vocabulary} {k : ℕ} (q : Query σ k) : DecidableEq (Work q) :=
  match q with
  | .emit φ ψ => inferInstanceAs (DecidableEq (FormulaProgram.Work φ ⊕ FormulaProgram.Work ψ))
  | .seq p q =>
      letI := workDecidableEq p
      letI := workDecidableEq q
      inferInstanceAs (DecidableEq (Work p ⊕ Work q))
  | .forEach p =>
      letI := workDecidableEq p
      inferInstanceAs (DecidableEq (LoopWork (Work p)))

def emptyEnv (n : ℕ) : TableEvaluation.TableEnv n [] := fun r => Fin.elim0 r

noncomputable def word {σ : Vocabulary} : {k : ℕ} → Query σ k →
    (A : OrderedStructure σ) → (Fin k → Fin A.size) → List Bool
  | _, .emit φ ψ, A, v =>
      if TableEvaluation.evaluate φ A v (emptyEnv A.size) then
        [TableEvaluation.evaluate ψ A v (emptyEnv A.size)] else []
  | _, .seq p q, A, v => word p A v ++ word q A v
  | _, .forEach p, A, v => (List.finRange A.size).flatMap (fun x => word p A (Fin.cons x v))

noncomputable def cost {σ : Vocabulary} : {k : ℕ} → Query σ k → Polynomial ℕ
  | _, .emit φ ψ => FormulaProgram.costPolynomial φ + FormulaProgram.costPolynomial ψ + 5
  | _, .seq p q => cost p + cost q
  | _, .forEach p => (cost p + 12) * Polynomial.X + 9

variable {K Aux : Type} [DecidableEq K]

def writeBit (out : K) : EvalProgram K Aux := .atom (.push out (fun s => s.1.2))

def compile {σ : Vocabulary} : {k : ℕ} → (q : Query σ k) →
    FormulaProgram.Inputs K σ k [] → K → (Work q → K) → EvalProgram K Aux
  | _, .emit φ ψ, input, out, work =>
      .seq (FormulaProgram.compile φ input (work ∘ Sum.inl))
        (.seq (.branch (fun s => s.1.2)
          (.seq (FormulaProgram.compile ψ input (work ∘ Sum.inr)) (writeBit out))
          (answer false)) (answer false))
  | _, .seq p q, input, out, work =>
      .seq (compile p input out (work ∘ Sum.inl)) (compile q input out (work ∘ Sum.inr))
  | _, .forEach p, input, out, work =>
      .seq (answer false)
        (StackFor.forValues input.domain (work .counter) (work .coordinate) (work .tmp)
          (compile p (input.existsPorts (work .coordinate)) out (work ∘ LoopWork.child)))

def written (out : K) (bits : List Bool) (s : EvalStore K Aux) : EvalStore K Aux :=
  StackTuples.setStack (result false s) out (bits.reverse ++ s.stk out)

theorem written_nil (out : K) (s : EvalStore K Aux) : written out [] s = result false s := by
  simp [written, StackTuples.setStack, result]

theorem written_append (out : K) (xs ys : List Bool) (s : EvalStore K Aux) :
    written out ys (written out xs s) = written out (xs ++ ys) s := by
  simp [written, StackTuples.setStack, result, List.reverse_append, List.append_assoc,
    Function.update_idem]

theorem written_represents {σ : Vocabulary} {k : ℕ} {input : FormulaProgram.Inputs K σ k []}
    {A : OrderedStructure σ} {v : Fin k → Fin A.size} {s : EvalStore K Aux} {out : K}
    (h : FormulaProgram.Represents input A v (emptyEnv A.size) s) (hf : input.Fresh out)
    (bits : List Bool) : FormulaProgram.Represents input A v (emptyEnv A.size) (written out bits s) :=
  (h.result false).setStack hf _

theorem written_clean {W : Type} {work : W → K} {s : EvalStore K Aux} {out : K}
    (h : FormulaProgram.Clean work s) (hf : ∀ w, work w ≠ out) (bits : List Bool) :
    FormulaProgram.Clean work (written out bits s) := (h.result false).setStack out hf _

def Correct {σ : Vocabulary} {k : ℕ} (q : Query σ k) : Prop :=
  ∀ (input : FormulaProgram.Inputs K σ k []) (out : K) (work : Work q → K),
    input.Safe → input.Fresh out → Function.Injective work →
    (∀ w, input.Fresh (work w)) → (∀ w, work w ≠ out) →
    ∀ (A : OrderedStructure σ) (v : Fin k → Fin A.size) (s : EvalStore K Aux),
      FormulaProgram.Clean work s → FormulaProgram.Represents input A v (emptyEnv A.size) s →
      ∃ c, c ≤ (cost q).eval A.size ∧ Executes (compile q input out work) s (written out (word q A v) s) c

theorem correct_emit {σ : Vocabulary} {k : ℕ} (φ ψ : RawFormula σ k []) :
    Correct (K := K) (Aux := Aux) (.emit φ ψ) := by
  intro input out work hs _ hi hf _ A v s hc hr
  have hwl : FormulaProgram.ValidWork input (work ∘ Sum.inl) :=
    ⟨fun _ _ h => Sum.inl.inj (hi h), fun w => hf (.inl w)⟩
  have hwr : FormulaProgram.ValidWork input (work ∘ Sum.inr) :=
    ⟨fun _ _ h => Sum.inr.inj (hi h), fun w => hf (.inr w)⟩
  obtain ⟨a, ha, hp⟩ := FormulaProgram.compile_correct φ input _ hs hwl A v _ s
    (fun w => hc (.inl w)) hr
  cases hb : TableEvaluation.evaluate φ A v (emptyEnv A.size) with
  | false =>
      rw [hb] at hp
      have hq := Executes.branch_false (p := .seq (FormulaProgram.compile ψ input (work ∘ Sum.inr))
        (writeBit out)) (b := fun s => s.1.2) rfl (answer_returns false (result false s))
      have hlast := answer_returns false (result false (result false s))
      have h := Executes.seq hp (Executes.seq hq hlast)
      refine ⟨a + 3, ?_, ?_⟩
      · simp only [cost, Polynomial.eval_add, Polynomial.eval_ofNat]
        omega
      · simpa [compile, word, hb, written_nil, result, Returns] using h
  | true =>
      rw [hb] at hp
      obtain ⟨b, hbnd, hq⟩ := FormulaProgram.compile_correct ψ input _ hs hwr A v _ (result true s)
        (fun w => hc (.inr w)) (hr.result true)
      let value := TableEvaluation.evaluate ψ A v (emptyEnv A.size)
      have hw := Executes.atom (.push out (fun s : ((Aux × Bool) × Bool) × Option Bool => s.1.2))
        (result value (result true s))
      have hbranch := Executes.branch_true (q := answer false) (b := fun s => s.1.2) rfl
        (Executes.seq hq hw)
      have hlast := answer_returns false
        (Op.apply (.push out (fun s : ((Aux × Bool) × Bool) × Option Bool => s.1.2))
          (result value (result true s)))
      have h := Executes.seq hp (Executes.seq hbranch hlast)
      refine ⟨a + (b + 3), ?_, ?_⟩
      · simp only [cost, Polynomial.eval_add, Polynomial.eval_ofNat]
        omega
      · simpa [compile, word, hb, written, StackTuples.setStack, writeBit, Returns,
          result, Op.apply, value, Function.update_idem, Nat.add_assoc] using h

theorem correct_seq {σ : Vocabulary} {k : ℕ} {p q : Query σ k}
    (hp : Correct (K := K) (Aux := Aux) p) (hq : Correct (K := K) (Aux := Aux) q) :
    Correct (K := K) (Aux := Aux) (.seq p q) := by
  intro input out work hs ho hi hf hw A v s hc hr
  obtain ⟨a, ha, hp⟩ := hp input out (work ∘ Sum.inl) hs ho
    (fun _ _ h => Sum.inl.inj (hi h)) (fun w => hf (.inl w)) (fun w => hw (.inl w))
    A v s (fun w => hc (.inl w)) hr
  obtain ⟨b, hb, hq⟩ := hq input out (work ∘ Sum.inr) hs ho
    (fun _ _ h => Sum.inr.inj (hi h)) (fun w => hf (.inr w)) (fun w => hw (.inr w))
    A v (written out (word p A v) s)
    (written_clean (fun w => hc (.inr w)) (fun w => hw (.inr w)) _)
    (written_represents hr ho _)
  refine ⟨a + b, ?_, ?_⟩
  · simpa [cost] using Nat.add_le_add ha hb
  · simpa only [compile, word, written_append] using Executes.seq hp hq

end Lax222097Proofs.QueryProgram
