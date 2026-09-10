import Lax429075.CircuitMachine
import Lax429075.TseitinCorrect
import Lax762056Proofs.CutMachine
import Lax762056Proofs.PolynomialComposition

namespace Lax762056Proofs.CookBridge

open Lax429075

def literal (l : CNF.Literal) : ShortCNF.Literal := (l.index, l.positive)
def formula (F : CNF.Formula) : ShortCNF.Formula := F.map (List.map literal)

theorem encodeList_map {α β : Type} (f : α → β) (e : β → List Bool) (d : α → List Bool)
    (h : ∀ a, e (f a) = d a) (xs : List α) :
    ShortCNF.encodeList e (xs.map f) = Encoding.encodeList d xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ShortCNF.encodeList, Encoding.encodeList, h, ih]

theorem encode_formula (F : CNF.Formula) : ShortCNF.encode (formula F) = Encoding.encodeCNF F := by
  apply encodeList_map
  intro C
  apply encodeList_map
  intro l
  simp [ShortCNF.encodeLiteral, literal, Encoding.encodeLiteral, Encoding.encodeNat, List.append_assoc]

theorem satisfiable_formula (F : CNF.Formula) :
    ShortCNF.Satisfiable (formula F) ↔ CNF.Satisfiable F := by
  simp only [ShortCNF.Satisfiable, formula, CNF.Satisfiable, CNF.eval, List.all_eq_true,
    List.forall_mem_map, List.any_map]
  rfl

theorem gate_short (i : ℕ) (g : Circuits.Gate) :
    ∀ D ∈ Tseitin.gateClauses i g, 1 ≤ D.length ∧ D.length ≤ 3 := by
  cases g <;> simp [Tseitin.gateClauses]

theorem tseitin_short (C : Circuits.Circuit) : ShortCNF.Short (formula (Tseitin.encode C)) := by
  intro D hD
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
  simp only [Tseitin.encode, List.mem_append, List.mem_singleton] at hE
  rcases hE with rfl | hE
  · simp
  · obtain ⟨⟨g, i⟩, _, hE⟩ := List.mem_flatMap.mp hE
    simpa using gate_short i g E hE

/-- The published circuit compiler already emits nonempty clauses of size
at most three, so its output can enter the Max Cut machine directly. -/
theorem compile (V : Lax434930.PolynomialTime.Language)
    (hV : V ∈ Lax434930.PolynomialTime.P) (p : Polynomial ℕ) :
    ∃ f : Lax434930.PolynomialTime.Word → Lax762056.GraphEncoding.Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id Lax762056.GraphEncoding.encode f) ∧
      ∀ x, (∃ y : Lax434930.PolynomialTime.Word,
        y.length ≤ p.eval x.length ∧ Lax434930.Certificates.pair x y ∈ V) ↔
        (f x).threshold ≤ Lax762056.MaxCut.maxCut (f x).graph := by
  obtain ⟨circuits, ⟨machine⟩, hc⟩ := CircuitMachine.compile V hV p
  let forms := fun x => formula (Tseitin.encode (circuits x))
  have hm : Turing.TM2ComputableInPolyTime id ShortCNF.encode forms := by
    refine { machine with outputsFun := ?_ }
    intro x
    simpa only [forms, encode_formula, id_eq] using machine.outputsFun x
  obtain ⟨hcut⟩ := CutMachine.polynomial_time
  refine ⟨CutEnumeration.output ∘ forms, PolynomialComposition.comp hm hcut, ?_⟩
  intro x
  rw [← hc x, ← TseitinCorrect.correct, ← satisfiable_formula]
  exact CutEnumeration.output_correct _ (tseitin_short _)

end Lax762056Proofs.CookBridge
