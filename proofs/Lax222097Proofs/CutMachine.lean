import Lax222097Proofs.CutEnumeration

namespace Lax222097Proofs.CutMachine

open CutEnumeration CNFWriter

/-- A nonempty fixed block, represented by a finite sequence of writes. -/
def block {k : ℕ} (b : Bool) : ℕ → Query k
  | 0 => .emit (.constant b)
  | n + 1 => .seq (.emit (.constant b)) (block b n)

theorem word_block {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (b : Bool) (n : ℕ) :
    word (block b n) F v = List.replicate (n + 1) b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [block, word, CNFAtom.value, ih, List.replicate_succ]

theorem flatMap_replicate {α : Type} (xs : List α) (n : ℕ) (b : Bool) :
    xs.flatMap (fun _ => List.replicate n b) = List.replicate (n * xs.length) b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, ih, List.length_cons, List.replicate_append_replicate]
    congr 1
    ring

def threshold : Query 0 :=
  .seq (.forEach (block true 21)) (.seq (block true 2) (.emit (.constant false)))

theorem word_threshold (F : ShortCNF.Formula) :
    word threshold F Fin.elim0 =
      List.replicate (22 * (ShortCNF.encode F).length + 3) true ++ [false] := by
  simp only [threshold, word, word_block, flatMap_replicate, List.length_finRange,
    CNFAtom.value]
  rw [← List.append_assoc, List.replicate_append_replicate]

def query : Query 0 :=
  .seq header (.seq (.emit (.constant false)) (.seq matrix threshold))

theorem word_encoding (F : ShortCNF.Formula) :
    word query F Fin.elim0 = Lax222097.GraphEncoding.encode (output F) := by
  simp only [query, word, word_header, word_matrix, word_threshold, CNFAtom.value,
    Lax222097.GraphEncoding.encode, Lax222097.GraphEncoding.unary, encoded_matrix]
  change _ = (List.replicate _ true ++ [false]) ++ matrixWord F ++
    (List.replicate (ShortCNF.toMaxCut F).threshold true ++ [false])
  rw [ShortCNF.maxCut_threshold]
  simp [output, List.append_assoc]

theorem polynomial_time :
    Nonempty (Turing.TM2ComputableInPolyTime ShortCNF.encode
      Lax222097.GraphEncoding.encode output) := by
  obtain ⟨m⟩ := CNFMachine.polynomial_time query
  refine ⟨{ m with outputsFun := ?_ }⟩
  intro F
  simpa only [id_eq, word_encoding] using m.outputsFun F

end Lax222097Proofs.CutMachine
