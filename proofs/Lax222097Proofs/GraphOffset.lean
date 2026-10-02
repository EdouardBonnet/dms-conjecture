import Lax222097Proofs.GraphEnumeration
import Mathlib.Order.Interval.Finset.Fin

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators

namespace Lax222097Proofs.GraphOffset

open Lax222097 Lax222097Proofs.QueryCompiler
open QueryProgram GraphFormulas GraphEnumeration

def spanTest : Formula 3 :=
  .conj (.conj (.less 2 1) (edge 2 1)) (.conj (lessEqual 2 0) (.less 0 1))

def query : GraphQuery.Q :=
  .forEach (.forEach (.forEach (.seq (.emit spanTest .truth) (.emit spanTest .truth))))

theorem value_spanTest {n : ℕ} (F : SimpleGraph (Fin n)) (a : Fin 3 → Fin n) :
    value F a spanTest = decide (a 2 < a 1 ∧ F.Adj (a 2) (a 1) ∧ a 2 ≤ a 0 ∧ a 0 < a 1) := by
  apply Bool.eq_iff_iff.mpr
  simp [spanTest, lessEqual, value_conj, value_less, value_edge, value_neg, and_assoc]

theorem flatMap_replicate {α : Type*} (xs : List α) (f : α → ℕ) (b : Bool) :
    xs.flatMap (fun x => List.replicate (f x) b) = List.replicate ((xs.map f).sum) b := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, ih, List.replicate_add]

theorem sum_span {n : ℕ} (u v : Fin n) :
    (∑ w : Fin n, if u ≤ w ∧ w < v then 2 else 0) = 2 * (v.val - u.val) := by
  have heq : (Finset.univ.filter (fun w => u ≤ w ∧ w < v)) = Finset.Ico u v := by
    ext w
    simp
  rw [← Finset.sum_filter, heq]
  simp [Nat.mul_comm]

theorem word_query {n : ℕ} (F : SimpleGraph (Fin n)) :
    word query (GraphQuery.source F) Fin.elim0 = List.replicate (Reduction.offset F) true := by
  have hbits (u v w : Fin n) :
      (if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then [true] else []) ++
        (if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then [true] else []) =
      List.replicate (if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then 2 else 0) true := by
    split <;> rfl
  simp only [query, word_forEach, word_seq, word_emit, value_spanTest, value_truth, decide_eq_true_eq]
  change (List.finRange n).flatMap (fun u => (List.finRange n).flatMap (fun v =>
    (List.finRange n).flatMap (fun w =>
      (if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then [true] else []) ++
      (if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then [true] else [])))) = _
  simp only [hbits, flatMap_replicate, ← Fin.sum_univ_def]
  congr 1
  have hinner (u v : Fin n) :
      (∑ w : Fin n, if u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v then 2 else 0) =
      if u < v ∧ F.Adj u v then 2 * (v.val - u.val) else 0 := by
    by_cases h : u < v ∧ F.Adj u v
    · simpa [h.1, h.2] using sum_span u v
    · have hfalse (w : Fin n) : ¬ (u < v ∧ F.Adj u v ∧ u ≤ w ∧ w < v) := by tauto
      simp [hfalse, h]
  simp only [hinner]
  unfold Reduction.offset MaxCut.edges
  rw [Finset.sum_filter, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split <;> simp_all

end Lax222097Proofs.GraphOffset
