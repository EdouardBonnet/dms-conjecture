import Lax222097Proofs.ReductionBasics
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ProdSigma

set_option backward.isDefEq.respectTransparency false

/-! A fixed enumeration of the retained vertices. The output labels are positions
in a filtered lexicographic list, so the specification never asks an algorithm
to compute a relabeling selected by `Fintype.equivFin`. -/

namespace Lax222097Proofs.EncodedReduction

open Lax222097 GraphEncoding

abbrev Raw (n : ℕ) := Fin n × Fin n × Bool × Fin n × Bool × Bool

/-- Represent a column by an input-vertex coordinate and one parity bit. -/
def column {n : ℕ} (x : Raw n) : ℕ :=
  2 * x.2.2.2.1.val + if x.2.2.2.2.1 then 1 else 0

def ambient (n : ℕ) : List (Raw n) :=
  (List.finRange n).product ((List.finRange n).product
    ([false, true].product ((List.finRange n).product ([false, true].product [false, true]))))

def Valid {n : ℕ} (F : SimpleGraph (Fin n)) (x : Raw n) : Prop :=
  (x.1 < x.2.1 ∧ F.Adj x.1 x.2.1) ∧
    ((column x = 2 * x.1.val ∧ x.2.2.2.2.2 = x.2.2.1) ∨
      (2 * x.1.val < column x ∧ column x < 2 * x.2.1.val) ∨
      (column x = 2 * x.2.1.val ∧ x.2.2.2.2.2 = !x.2.2.1))

noncomputable def labels {n : ℕ} (F : SimpleGraph (Fin n)) : List (Raw n) := by
  classical
  exact (ambient n).filter (fun x => decide (Valid F x))

theorem mem_ambient {n : ℕ} (x : Raw n) : x ∈ ambient n := by
  rcases x with ⟨u, v, t, j, p, s⟩
  cases t <;> cases p <;> cases s <;> simp [ambient]

theorem nodup_ambient (n : ℕ) : (ambient n).Nodup :=
  (List.nodup_finRange n).product ((List.nodup_finRange n).product
    ((by decide : [false, true].Nodup).product
      ((List.nodup_finRange n).product ((by decide : [false, true].Nodup).product (by decide)))))

theorem mem_labels {n : ℕ} (F : SimpleGraph (Fin n)) (x : Raw n) :
    x ∈ labels F ↔ Valid F x := by
  classical
  simp [labels, mem_ambient]

theorem nodup_labels {n : ℕ} (F : SimpleGraph (Fin n)) : (labels F).Nodup := by
  classical
  exact (nodup_ambient n).filter _

def forget {n : ℕ} {F : SimpleGraph (Fin n)} (x : ↥(Reduction.retainedVertices F)) : Raw n :=
  (x.val.1.1.val.1, x.val.1.1.val.2, x.val.1.2,
    ⟨x.val.2.1.val / 2, by have h := x.val.2.1.isLt; omega⟩,
    decide (x.val.2.1.val % 2 = 1), x.val.2.2)

theorem column_forget {n : ℕ} {F : SimpleGraph (Fin n)} (x : ↥(Reduction.retainedVertices F)) :
    column (forget x) = x.val.2.1.val := by
  by_cases h : x.val.2.1.val % 2 = 1 <;> simp [column, forget, h] <;> omega

theorem valid_forget {n : ℕ} {F : SimpleGraph (Fin n)} (x : ↥(Reduction.retainedVertices F)) :
    Valid F (forget x) := by
  refine ⟨x.val.1.1.property, ?_⟩
  simp only [column_forget]
  exact x.property

theorem column_lt {n : ℕ} {F : SimpleGraph (Fin n)} {x : Raw n} (h : Valid F x) :
    column x < 2 * n - 1 := by
  have hv := x.2.1.isLt
  have hu := x.1.isLt
  rcases h.2 with ⟨ha, _⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ <;> omega

def retain {n : ℕ} {F : SimpleGraph (Fin n)} (x : Raw n) (h : Valid F x) :
    ↥(Reduction.retainedVertices F) :=
  ⟨((⟨(x.1, x.2.1), h.1⟩, x.2.2.1), ⟨column x, column_lt h⟩, x.2.2.2.2.2), h.2⟩

theorem forget_retain {n : ℕ} {F : SimpleGraph (Fin n)} (x : Raw n) (h : Valid F x) :
    forget (retain x h) = x := by
  rcases x with ⟨u, v, t, w, p, s⟩
  cases p <;> simp [forget, retain, column, Nat.add_div]

theorem retain_forget {n : ℕ} {F : SimpleGraph (Fin n)} (x : ↥(Reduction.retainedVertices F)) :
    retain (forget x) (valid_forget x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext
      exact column_forget x
    · rfl

noncomputable def retainedEquiv {n : ℕ} (F : SimpleGraph (Fin n)) :
    {x // x ∈ labels F} ≃ ↥(Reduction.retainedVertices F) where
  toFun x := retain x.val ((mem_labels F x.val).mp x.property)
  invFun x := ⟨forget x, (mem_labels F (forget x)).mpr (valid_forget x)⟩
  left_inv x := by apply Subtype.ext; exact forget_retain _ _
  right_inv x := retain_forget x

noncomputable def vertexEquiv {n : ℕ} (F : SimpleGraph (Fin n)) :
    Fin (labels F).length ≃ ↥(Reduction.retainedVertices F) :=
  (List.Nodup.getEquiv (labels F) (nodup_labels F)).trans (retainedEquiv F)

noncomputable def reduce (I : Instance) : Instance where
  order := (labels I.graph).length
  graph := (Reduction.reductionGraph I.graph).comap (vertexEquiv I.graph)
  threshold := I.threshold + Reduction.offset I.graph

noncomputable def iso (I : Instance) : (reduce I).graph ≃g Reduction.reductionGraph I.graph where
  toEquiv := vertexEquiv I.graph
  map_rel_iff' := Iff.rfl

theorem threshold (I : Instance) : (reduce I).threshold = I.threshold + Reduction.offset I.graph := rfl

theorem length_product {α β : Type*} (xs : List α) (ys : List β) :
    (xs.product ys).length = xs.length * ys.length := List.length_product xs ys

theorem length_ambient (n : ℕ) : (ambient n).length = 8 * n ^ 3 := by
  simp [ambient, length_product]
  ring

theorem order_le (I : Instance) : (reduce I).order ≤ 8 * I.order ^ 3 := by
  classical
  have hl : (labels I.graph).length ≤ (ambient I.order).length := List.length_filter_le _ _
  rw [length_ambient] at hl
  exact hl

end Lax222097Proofs.EncodedReduction
