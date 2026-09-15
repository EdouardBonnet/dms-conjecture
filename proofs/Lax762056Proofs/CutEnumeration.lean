import Lax762056Proofs.CutTests
import Lax762056Proofs.MaxCutIso

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.CutEnumeration

open CutVertices CNFWriter CutTests

def constantsQuery {k : ℕ} (body : ConstTag → Query k) : Query k :=
  .seq (body (.core false)) (.seq (body (.core true))
    (.seq (body (.variablePath false)) (body (.variablePath true))))

def vertices {k : ℕ} (body : VarTag → Query (k + 1)) (fixed : ConstTag → Query k) : Query k :=
  tags.foldr (fun tag rest => .seq (.forEach (body tag)) rest) (constantsQuery fixed)

theorem word_fold {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (body : VarTag → Query (k + 1))
    (rest : Query k) (ts : List VarTag) :
    word (ts.foldr (fun tag rest => .seq (.forEach (body tag)) rest) rest) F v =
      ts.flatMap (fun tag => (List.finRange (ShortCNF.encode F).length).flatMap
        (fun x => word (body tag) F (Fin.cons x v))) ++ word rest F v := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [word, ih, List.append_assoc]

theorem word_vertices {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (body : VarTag → Query (k + 1))
    (fixed : ConstTag → Query k) :
    word (vertices body fixed) F v = (labels (ShortCNF.encode F).length).flatMap
      (fun x => match x with
        | .inl (tag, i) => word (body tag) F (Fin.cons i v)
        | .inr tag => word (fixed tag) F v) := by
  rw [vertices, word_fold]
  simp [labels, constantsQuery, constants, word, List.product, List.flatMap_assoc,
    List.flatMap_map, List.append_assoc]

def header : Query 0 :=
  vertices (fun _ => .emit (.constant true)) (fun _ => .emit (.constant true))

theorem word_header (F : ShortCNF.Formula) :
    word header F Fin.elim0 = List.replicate (labels (ShortCNF.encode F).length).length true := by
  rw [header, word_vertices]
  have h (x : Raw (ShortCNF.encode F).length) :
      (match x with
        | .inl (_, i) => word (.emit (.constant true)) F (Fin.cons i Fin.elim0)
        | .inr _ => word (.emit (.constant true)) F Fin.elim0) = [true] := by
    cases x <;> rfl
  simp only [h, ← List.map_eq_flatMap]
  simp

def row {k : ℕ} (x : Raw k) : Query k :=
  vertices (fun tag => .emit (rawTest (mapRaw Fin.succ x) (.inl (tag, 0))))
    (fun tag => .emit (rawTest x (.inr tag)))

theorem mapRaw_cons {k n : ℕ} (v : Fin k → Fin n) (i : Fin n) (x : Raw k) :
    mapRaw (Fin.cons i v) (mapRaw Fin.succ x) = mapRaw v x := by
  rcases x with ⟨tag, j⟩ | tag <;> rfl

theorem word_row {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x : Raw k) :
    word (row x) F v = (labels (ShortCNF.encode F).length).map (fun y =>
      decide ((ShortCNF.toMaxCut F).graph.Adj
        (rawFinEquiv _ (mapRaw v x)) (rawFinEquiv _ y))) := by
  rw [row, word_vertices, List.map_eq_flatMap]
  apply congrArg (fun f => (labels (ShortCNF.encode F).length).flatMap f)
  funext y
  rcases y with ⟨tag, i⟩ | tag
  · simp only [word, rawTest_correct, mapRaw_cons]
    rfl
  · simp only [word, rawTest_correct]
    rfl

def matrix : Query 0 :=
  vertices (fun tag => row (.inl (tag, 0))) (fun tag => row (.inr tag))

def matrixWord (F : ShortCNF.Formula) : List Bool :=
  (labels (ShortCNF.encode F).length).flatMap (fun x =>
    (labels (ShortCNF.encode F).length).map (fun y =>
      decide ((ShortCNF.toMaxCut F).graph.Adj (rawFinEquiv _ x) (rawFinEquiv _ y))))

theorem word_matrix (F : ShortCNF.Formula) : word matrix F Fin.elim0 = matrixWord F := by
  rw [matrix, word_vertices, matrixWord]
  apply congrArg (fun f => (labels (ShortCNF.encode F).length).flatMap f)
  funext x
  rcases x with ⟨tag, i⟩ | tag <;> simp only [word_row] <;> rfl

def output (F : ShortCNF.Formula) : Lax762056.GraphEncoding.Instance where
  order := (labels (ShortCNF.encode F).length).length
  graph := (ShortCNF.toMaxCut F).graph.comap (labelEquiv (ShortCNF.encode F).length)
  threshold := (ShortCNF.toMaxCut F).threshold

def outputIso (F : ShortCNF.Formula) : (output F).graph ≃g (ShortCNF.toMaxCut F).graph where
  toEquiv := labelEquiv (ShortCNF.encode F).length
  map_rel_iff' := by intro _ _; rfl

theorem output_correct (F : ShortCNF.Formula) (hF : ShortCNF.Short F) :
    ShortCNF.Satisfiable F ↔ (output F).threshold ≤ Lax762056.MaxCut.maxCut (output F).graph := by
  rw [MaxCutIso.maxCut_eq (outputIso F)]
  exact ShortCNF.maxCut_correct F hF

theorem encoded_matrix (F : ShortCNF.Formula) :
    (List.finRange (output F).order).flatMap (fun u =>
      (List.finRange (output F).order).map (fun v => decide ((output F).graph.Adj u v))) =
      matrixWord F := by
  have hadj (u v : Fin (labels (ShortCNF.encode F).length).length) :
      (output F).graph.Adj u v ↔ (ShortCNF.toMaxCut F).graph.Adj
        (rawFinEquiv _ ((labels (ShortCNF.encode F).length).get u))
        (rawFinEquiv _ ((labels (ShortCNF.encode F).length).get v)) := by rfl
  change (List.finRange (labels (ShortCNF.encode F).length).length).flatMap _ = _
  simp only [hadj]
  unfold matrixWord
  conv_rhs => rw [← List.map_get_finRange (labels (ShortCNF.encode F).length)]
  simp only [List.flatMap_map, List.map_map, Function.comp_def]
  rfl

end Lax762056Proofs.CutEnumeration
