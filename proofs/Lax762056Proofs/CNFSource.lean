import Lax762056Proofs.CNFAtomLiteral
import Lax762056Proofs.QueryLoop

namespace Lax762056Proofs.CNFSource

open Lax762056Proofs.QueryDefinitions.OrderedStructures Lax762056Proofs.QueryCompiler StackBoolean

/-- The input word itself, viewed as one unary relation on its positions. -/
def source (F : ShortCNF.Formula) : OrderedStructure [1] where
  size := (ShortCNF.encode F).length
  relation r := by
    refine Fin.cases ?_ (fun i => Fin.elim0 i) r
    change (Fin 1 → Fin (ShortCNF.encode F).length) → Bool
    exact fun v => (ShortCNF.encode F).get (v 0)

theorem source_table (F : ShortCNF.Formula) (r : Fin [1].length) :
    (Lax762056Proofs.QueryDefinitions.StructureEncoding.tuples (ShortCNF.encode F).length ([1].get r)).map
      ((source F).relation r) = ShortCNF.encode F := by
  fin_cases r
  simp [source, Lax762056Proofs.QueryDefinitions.StructureEncoding.tuples, List.map_flatMap]
  simp only [← List.map_eq_flatMap]
  exact List.map_get_finRange _

def ports {K : Type} {k : ℕ} (input : FormulaProgram.Inputs K [1] k []) : CNFAtom.Inputs K k where
  word := input.symbol 0
  domain := input.domain
  coordinate := input.element

theorem fresh {K : Type} {k : ℕ} {input : FormulaProgram.Inputs K [1] k []} {key : K}
    (h : input.Fresh key) : (ports input).Fresh key := ⟨h.2.2.1 0, h.1, h.2.1⟩

theorem represents {K Aux : Type} {k : ℕ} {input : FormulaProgram.Inputs K [1] k []}
    {F : ShortCNF.Formula} {v : Fin k → Fin (ShortCNF.encode F).length} {s : EvalStore K Aux}
    (h : FormulaProgram.Represents input (source F) v (QueryProgram.emptyEnv (source F).size) s) :
    CNFAtom.Represents (ports input) F v s := by
  refine ⟨?_, h.domain, h.element⟩
  exact (h.symbol 0).trans (source_table F 0)

end Lax762056Proofs.CNFSource
