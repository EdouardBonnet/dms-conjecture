import Lax762056Proofs.QueryBounds
import Lax762056Proofs.EncodingFacts
import Lax762056Proofs.PolynomialComposition
import Lax762056Proofs.QueryCompiler.StackUnary
import Lax762056Proofs.QueryCompiler.StackReadTable

namespace Lax762056Proofs.GraphQuery

open Lax762056 GraphEncoding Lax762056Proofs.QueryDefinitions.OrderedStructures Lax762056Proofs.QueryDefinitions.FixedPointSyntax
open Lax762056Proofs.QueryCompiler StackProgram StackBoolean

abbrev Q := QueryProgram.Query [2] 0

noncomputable def matrix {n : ℕ} (F : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => decide (F.Adj u v)))

theorem matrix_length {n : ℕ} (F : SimpleGraph (Fin n)) : (matrix F).length = n ^ 2 := by
  classical
  simp [matrix, List.length_flatMap, List.sum_replicate, pow_two]

theorem encode_eq (I : Instance) : encode I = unary I.order ++ matrix I.graph ++ unary I.threshold := rfl

noncomputable def source {n : ℕ} (F : SimpleGraph (Fin n)) : OrderedStructure [2] where
  size := n
  relation r := by
    classical
    refine Fin.cases ?_ (fun i => Fin.elim0 i) r
    change (Fin 2 → Fin n) → Bool
    exact fun a => decide (F.Adj (a 0) (a 1))

theorem source_table {n : ℕ} (F : SimpleGraph (Fin n)) (r : Symbol [2]) :
    (Lax762056Proofs.QueryDefinitions.StructureEncoding.tuples n ([2].get r)).map ((source F).relation r) = matrix F := by
  classical
  fin_cases r
  simp [source, matrix, Lax762056Proofs.QueryDefinitions.StructureEncoding.tuples, List.map_flatMap, List.map_map,
    Function.comp_def]
  simp only [← List.map_eq_flatMap]

inductive Port (q : Q)
  | input | output | acc | domain | table | count | tmp | rev
  | power (i : Fin 2)
  | query (w : QueryProgram.Work q)
  deriving DecidableEq, Fintype

def initial : ((Unit × Bool) × Bool) × Option Bool := ((((), true), false), none)

def inputs (q : Q) : FormulaProgram.Inputs (Port q) [2] 0 [] where
  domain := .domain
  element := Fin.elim0
  symbol := fun _ => .table
  relation := Fin.elim0

def readMatrix (q : Q) : EvalProgram (Port q) Unit :=
  StackReadTable.readTable .domain .input .table .count .tmp .rev [.power 0, .power 1]

def finish (q : Q) : EvalProgram (Port q) Unit :=
  .seq (StackTransfer.transfer .input .acc)
    (.seq (StackClear.clear .domain)
      (.seq (StackClear.clear .table)
        (.seq (StackTransfer.transfer .acc .output) (answer false))))

def program (q : Q) : EvalProgram (Port q) Unit :=
  .seq (StackUnary.parse .input .domain)
    (.seq (readMatrix q)
      (.seq (QueryProgram.compile q (inputs q) .acc Port.query) (finish q)))

noncomputable def afterUnary (q : Q) (I : Instance) : EvalStore (Port q) Unit where
  state := (initial.1, some false)
  stk k := match k with
    | .input => matrix I.graph ++ unary I.threshold
    | .domain => List.replicate I.order true
    | _ => []

noncomputable def prepared (q : Q) (I : Instance) : EvalStore (Port q) Unit where
  state := initial
  stk k := match k with
    | .input => unary I.threshold
    | .domain => List.replicate I.order true
    | .table => matrix I.graph
    | _ => []

noncomputable def render (q : Q) (I : Instance) : List Bool :=
  QueryProgram.word q (source I.graph) Fin.elim0 ++ unary I.threshold

noncomputable def time (q : Q) : Polynomial ℕ :=
  StackReadTable.costPolynomial 2 + 4 * QueryProgram.cost q +
    2 * Polynomial.X ^ 2 + 11 * Polynomial.X + 20

theorem split_unary (n : ℕ) (tail : List Bool) : StackUnary.splitUnary (unary n ++ tail) = (n, some tail) := by
  induction n with
  | zero => simp [unary, StackUnary.splitUnary]
  | succ n ih =>
      have h := congrArg (fun r : ℕ × Option (List Bool) => (r.1 + 1, r.2)) ih
      simpa [unary, List.replicate_succ, StackUnary.splitUnary] using h

theorem parse_executes (q : Q) (I : Instance) :
    Executes (StackUnary.parse .input .domain) (ioStore (Port.input : Port q) initial (encode I))
      (afterUnary q I) (3 * I.order + 2) := by
  have h := StackUnary.parse_executes (K := Port q) (fun _ => []) .input .domain (by simp)
    (encode I) [] initial.1 initial.2
  have he : StackUnary.splitUnary (encode I) = (I.order, some (matrix I.graph ++ unary I.threshold)) := by
    rw [encode_eq, List.append_assoc, split_unary]
  rw [he] at h
  have hin : StackTransfer.working (fun _ : Port q => []) .input .domain (encode I) [] initial.1 initial.2 =
      ioStore (Port.input : Port q) initial (encode I) := by
    apply Store.ext
    · rfl
    · funext k
      cases k <;> simp [StackTransfer.working, ioStore]
  have hout : StackTransfer.working (fun _ : Port q => []) .input .domain
      (matrix I.graph ++ unary I.threshold) (List.replicate I.order true ++ [])
      initial.1 (StackUnary.finished (some (matrix I.graph ++ unary I.threshold))) = afterUnary q I := by
    apply Store.ext
    · rfl
    · funext k
      cases k <;> simp [StackTransfer.working, afterUnary]
  simpa only [hin, hout, Option.getD_some] using h

theorem readMatrix_executes (q : Q) (I : Instance) :
    ∃ c, c ≤ (StackReadTable.costPolynomial 2).eval I.order ∧
      Executes (readMatrix q) (afterUnary q I) (prepared q I) c := by
  obtain ⟨c, hc, h⟩ := StackReadTable.readTable_executes (K := Port q)
    .domain .input .table .count .tmp .rev
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    [.power 0, .power 1] (by simp) (by simp)
    I.order (afterUnary q I) rfl rfl rfl rfl rfl (by simp [afterUnary])
  have he : StackReadTable.result (Port.input : Port q) .table I.order 2 (afterUnary q I) = prepared q I := by
    have hl : I.order ^ 2 ≤ (matrix I.graph ++ unary I.threshold).length := by
      simp [matrix_length]
    have ht : (matrix I.graph ++ unary I.threshold).take (I.order ^ 2) = matrix I.graph := by
      rw [← matrix_length I.graph]; simp
    have hd : (matrix I.graph ++ unary I.threshold).drop (I.order ^ 2) = unary I.threshold := by
      rw [← matrix_length I.graph]; simp
    apply Store.ext
    · simp [StackReadTable.result, afterUnary, prepared, initial]
    · funext k
      cases k <;> simp [StackReadTable.result, StackTake.prefix_eq_take _ _ hl, ht, hd,
        afterUnary, prepared]
  exact ⟨c, hc, by simpa only [readMatrix, List.length_cons, List.length_nil, he] using h⟩

end Lax762056Proofs.GraphQuery
