import Lax762056Proofs.GraphFormulas

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical

namespace Lax762056Proofs.GraphEnumeration

open Lax762056 Lax762056Proofs.QueryCompiler
open QueryProgram GraphFormulas EncodedReduction

theorem word_emit {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (φ ψ : Formula k) :
    word (.emit φ ψ) (GraphQuery.source F) a =
      if value F a φ then [value F a ψ] else [] := rfl

theorem word_seq {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (p q : Query [2] k) :
    word (.seq p q) (GraphQuery.source F) a =
      word p (GraphQuery.source F) a ++ word q (GraphQuery.source F) a := rfl

theorem word_forEach {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (p : Query [2] (k + 1)) :
    word (.forEach p) (GraphQuery.source F) a =
      (List.finRange n).flatMap (fun x => word p (GraphQuery.source F) (Fin.cons x a)) := rfl

def four {k : ℕ} (body : Bool → Bool → Query [2] k) : Query [2] k :=
  .seq (.seq (body false false) (body false true))
    (.seq (body true false) (body true true))

/-- The input coordinates are visited in precisely the order of `ambient`. -/
def vertices {k : ℕ} (body : Bool → Bool → Bool → Query [2] (k + 3)) : Query [2] k :=
  .forEach (.forEach
    (.seq (.forEach (four (body false))) (.forEach (four (body true)))))

def extend {n k : ℕ} (a : Fin k → Fin n) (x : Raw n) : Fin (k + 3) → Fin n :=
  Fin.cons x.2.2.2.1 (Fin.cons x.2.1 (Fin.cons x.1 a))

theorem word_vertices {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (body : Bool → Bool → Bool → Query [2] (k + 3)) :
    word (vertices body) (GraphQuery.source F) a =
      (ambient n).flatMap (fun x =>
        word (body x.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) (GraphQuery.source F) (extend a x)) := by
  simp [vertices, four, word, ambient, List.product, List.flatMap_assoc,
    List.flatMap_append, List.flatMap_map, extend, GraphQuery.source, List.append_assoc]

theorem flatMap_filter {α β : Type*} (xs : List α) (p : α → Bool) (f : α → List β) :
    xs.flatMap (fun x => if p x then f x else []) = (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

def header : GraphQuery.Q :=
  vertices (fun t p s => .emit (kept 2 1 0 t p s) .truth)

def matrix : GraphQuery.Q :=
  vertices (fun t p s => vertices (fun t' p' s' =>
    .emit (.conj (kept 5 4 3 t p s) (kept 2 1 0 t' p' s'))
      (adjacent 5 4 3 2 1 0 t p s t' p' s')))

theorem word_header {n : ℕ} (F : SimpleGraph (Fin n)) :
    word header (GraphQuery.source F) Fin.elim0 = List.replicate (labels F).length true := by
  rw [header, word_vertices]
  have hraw (x : Raw n) : raw (extend Fin.elim0 x) 2 1 0 x.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 = x := by
    rfl
  simp only [word_emit, value_kept, hraw, value_truth]
  change (ambient n).flatMap (fun x => if decide (Valid F x) then [true] else []) = _
  rw [flatMap_filter]
  simp [← List.map_eq_flatMap, labels]

theorem word_matrix {n : ℕ} (F : SimpleGraph (Fin n)) :
    word matrix (GraphQuery.source F) Fin.elim0 =
      (labels F).flatMap (fun x => (labels F).map (fun y => decide (rawAdjacent x y))) := by
  rw [matrix, word_vertices]
  simp only [word_vertices, word_emit, value_conj, value_kept, value_adjacent]
  have hraw (x y : Raw n) :
      raw (extend (extend Fin.elim0 x) y) 5 4 3 x.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 = x := by rfl
  have hraw' (x y : Raw n) :
      raw (extend (extend Fin.elim0 x) y) 2 1 0 y.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 = y := by rfl
  simp only [hraw, hraw']
  have hrow (x : Raw n) :
      (ambient n).flatMap (fun y =>
        if decide (Valid F x) && decide (Valid F y) then [decide (rawAdjacent x y)] else []) =
      if decide (Valid F x) then (labels F).map (fun y => decide (rawAdjacent x y)) else [] := by
    by_cases hx : Valid F x
    · simp only [hx, decide_true, Bool.true_and, Bool.true_eq, if_true]
      rw [flatMap_filter]
      simp [labels, ← List.map_eq_flatMap]
    · simp [hx]
  calc
    _ = (ambient n).flatMap (fun x => if decide (Valid F x) then
        (labels F).map (fun y => decide (rawAdjacent x y)) else []) := by
      apply congrArg (fun f : Raw n → List Bool => (ambient n).flatMap f)
      funext x
      exact hrow x
    _ = _ := flatMap_filter _ _ _

theorem encoded_matrix (I : GraphEncoding.Instance) :
    GraphQuery.matrix (reduce I).graph =
      (labels I.graph).flatMap (fun x =>
        (labels I.graph).map (fun y => decide (rawAdjacent x y))) := by
  have hadj (u v : Fin (labels I.graph).length) :
      (reduce I).graph.Adj u v ↔
        rawAdjacent ((labels I.graph).get u) ((labels I.graph).get v) := by
    exact retained_adjacent _ _
      ((mem_labels _ _).mp (List.get_mem _ _)) ((mem_labels _ _).mp (List.get_mem _ _))
  unfold GraphQuery.matrix
  simp only [hadj]
  conv_rhs => rw [← List.map_get_finRange (labels I.graph)]
  simp only [List.flatMap_map, List.map_map, Function.comp_def]
  rfl

end Lax762056Proofs.GraphEnumeration
