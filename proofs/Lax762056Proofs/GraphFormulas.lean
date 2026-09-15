import Lax762056Proofs.GraphQueryRun

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.GraphFormulas

open Lax762056 Lax762056Proofs.QueryDefinitions.OrderedStructures Lax762056Proofs.QueryDefinitions.FixedPointSyntax
open Lax762056Proofs.QueryCompiler

abbrev Formula (k : ℕ) := RawFormula [2] k []

def constant {k : ℕ} (b : Bool) : Formula k := if b then .truth else .neg .truth

def either {k : ℕ} (p q : Formula k) : Formula k := .neg (.conj (.neg p) (.neg q))

def lessEqual {k : ℕ} (x y : Fin k) : Formula k := .neg (.less y x)

def edge {k : ℕ} (x y : Fin k) : Formula k := by
  refine .relation 0 ?_
  change Fin 2 → Fin k
  exact Fin.cases x (Fin.cases y Fin.elim0)

def successor {k : ℕ} (x y : Fin k) : Formula k :=
  .conj (.less x y) (.neg (.exists' (.conj (.less x.succ 0) (.less 0 y.succ))))

def kept {k : ℕ} (u v w : Fin k) (tag parity side : Bool) : Formula k :=
  .conj (.conj (.less u v) (edge u v))
    (if parity then .conj (lessEqual u w) (.less w v)
    else either (.conj (.equal w u) (constant (decide (side = tag))))
      (either (.conj (.less u w) (.less w v))
        (.conj (.equal w v) (constant (decide (side = !tag))))))

def nextColumn {k : ℕ} (w w' : Fin k) (p p' : Bool) : Formula k :=
  if p then (if p' then constant false else successor w w')
  else (if p' then .equal w w' else constant false)

def adjacent {k : ℕ} (u v w u' v' w' : Fin k) (t p s t' p' s' : Bool) : Formula k :=
  either (.conj (.equal w w') (constant (decide (p = p' ∧ s ≠ s'))))
    (.conj (.conj (.equal u u') (.conj (.equal v v') (constant (decide (t = t')))))
      (either (nextColumn w w' p p') (nextColumn w' w p' p)))

abbrev value {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (φ : Formula k) : Bool :=
  TableEvaluation.evaluate φ (GraphQuery.source F) a (QueryProgram.emptyEnv n)

theorem value_truth {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) :
    value F a .truth = true := rfl

theorem value_equal {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (u v : Fin k) :
    value F a (.equal u v) = decide (a u = a v) := rfl

theorem value_less {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (u v : Fin k) :
    value F a (.less u v) = decide (a u < a v) := rfl

theorem value_conj {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (φ ψ : Formula k) :
    value F a (.conj φ ψ) = (value F a φ && value F a ψ) := rfl

theorem value_neg {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (φ : Formula k) :
    value F a (.neg φ) = !value F a φ := rfl

theorem value_constant {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (b : Bool) :
    value F a (constant b) = b := by cases b <;> rfl

theorem value_either {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (φ ψ : Formula k) :
    value F a (either φ ψ) = (value F a φ || value F a ψ) := by
  simp [value, either, TableEvaluation.evaluate]

theorem value_edge {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (u v : Fin k) :
    value F a (edge u v) = decide (F.Adj (a u) (a v)) := by
  classical
  rfl

theorem successor_iff {n : ℕ} (a b : Fin n) :
    (a < b ∧ ∀ c : Fin n, ¬ (a < c ∧ c < b)) ↔ a.val + 1 = b.val := by
  constructor
  · rintro ⟨hab, h⟩
    by_contra he
    have hc : a.val + 1 < n := by omega
    exact h ⟨a.val + 1, hc⟩ ⟨by change a.val < a.val + 1; omega,
      by change a.val + 1 < b.val; omega⟩
  · intro h
    refine ⟨by change a.val < b.val; omega, ?_⟩
    intro c hc
    have h₁ : a.val < c.val := hc.1
    have h₂ : c.val < b.val := hc.2
    omega

theorem value_successor {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n) (u v : Fin k) :
    value F a (successor u v) = decide ((a u).val + 1 = (a v).val) := by
  apply Bool.eq_iff_iff.mpr
  simpa [value, successor, TableEvaluation.evaluate, not_and, not_lt] using!
    successor_iff (a u) (a v)

def raw {n k : ℕ} (a : Fin k → Fin n) (u v w : Fin k) (t p s : Bool) : EncodedReduction.Raw n :=
  (a u, a v, t, a w, p, s)

theorem value_kept {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (u v w : Fin k) (t p s : Bool) :
    value F a (kept u v w t p s) = decide (EncodedReduction.Valid F (raw a u v w t p s)) := by
  classical
  apply Bool.eq_iff_iff.mpr
  cases p <;> cases t <;> cases s <;>
    simp [kept, value_either, value_constant, value_edge, lessEqual, value_conj, value_less, value_equal, value_neg,
      EncodedReduction.Valid, raw, EncodedReduction.column, Fin.ext_iff]
  all_goals omega

def rawAdjacent {n : ℕ} (x y : EncodedReduction.Raw n) : Prop :=
  (EncodedReduction.column x = EncodedReduction.column y ∧ x.2.2.2.2.2 ≠ y.2.2.2.2.2) ∨
    (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
      (EncodedReduction.column x + 1 = EncodedReduction.column y ∨
        EncodedReduction.column y + 1 = EncodedReduction.column x))

theorem value_nextColumn {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (w w' : Fin k) (p p' : Bool) :
    value F a (nextColumn w w' p p') =
      decide (2 * (a w).val + (if p then 1 else 0) + 1 =
        2 * (a w').val + (if p' then 1 else 0)) := by
  apply Bool.eq_iff_iff.mpr
  cases p <;> cases p' <;>
    simp [nextColumn, value_constant, value_successor, TableEvaluation.evaluate, Fin.ext_iff]
  all_goals omega

theorem value_adjacent {n k : ℕ} (F : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (u v w u' v' w' : Fin k) (t p s t' p' s' : Bool) :
    value F a (adjacent u v w u' v' w' t p s t' p' s') =
      decide (rawAdjacent (raw a u v w t p s) (raw a u' v' w' t' p' s')) := by
  apply Bool.eq_iff_iff.mpr
  have heo (i j : ℕ) : 2 * i ≠ 2 * j + 1 := by omega
  have hoe (i j : ℕ) : 2 * i + 1 ≠ 2 * j := by omega
  cases p <;> cases p' <;>
    simp [adjacent, value_either, value_constant, value_nextColumn, value_conj, value_equal,
      rawAdjacent, raw, EncodedReduction.column, Fin.ext_iff, and_assoc, heo, hoe]

theorem retained_adjacent {n : ℕ} {F : SimpleGraph (Fin n)} (x y : EncodedReduction.Raw n)
    (hx : EncodedReduction.Valid F x) (hy : EncodedReduction.Valid F y) :
    (Reduction.reductionGraph F).Adj (EncodedReduction.retain x hx) (EncodedReduction.retain y hy) ↔
      rawAdjacent x y := by
  change (ColumnGraph.columnGraph (Reduction.Row F) (2 * n - 1)).Adj _ _ ↔ _
  rw [ReductionBasics.column_adj]
  simp [EncodedReduction.retain, rawAdjacent, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff, and_assoc]

end Lax762056Proofs.GraphFormulas
