import Lax762056.IndependenceIdentity
import Mathlib.Tactic

namespace Lax762056Proofs.ReductionBasics

open Lax762056

theorem column_adj {R : Type*} {c : ℕ} (x y : ColumnGraph.Vertex R c) :
    (ColumnGraph.graph R c).Adj x y ↔
    (x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
    (x.1 = y.1 ∧ (x.2.1.val + 1 = y.2.1.val ∨ y.2.1.val + 1 = x.2.1.val)) := by
  rw [ColumnGraph.graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
      · exact Or.inr ⟨h1.symm, Or.inr h2⟩
      · exact Or.inr ⟨h1.symm, Or.inl h2⟩
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    subst y
    rcases h with ⟨_, h⟩ | ⟨_, h | h⟩
    · exact h rfl
    · omega
    · omega

abbrev Vtx {n : ℕ} (F : SimpleGraph (Fin n)) := ↥(Reduction.kept F)

noncomputable instance edgeFintype {n : ℕ} (F : SimpleGraph (Fin n)) :
    Fintype (Reduction.Edge F) := Fintype.ofFinite _

abbrev row {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F) := x.val.1
abbrev col {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F) := x.val.2.1.val
abbrev side {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F) := x.val.2.2
abbrev lo {n : ℕ} {F : SimpleGraph (Fin n)} (e : Reduction.Edge F) := e.val.1.val
abbrev hi {n : ℕ} {F : SimpleGraph (Fin n)} (e : Reduction.Edge F) := e.val.2.val
abbrev span {n : ℕ} {F : SimpleGraph (Fin n)} (e : Reduction.Edge F) := hi e - lo e

theorem lo_lt_hi {n : ℕ} {F : SimpleGraph (Fin n)} (e : Reduction.Edge F) :
    lo e < hi e := e.property.1

theorem adj {n : ℕ} {F : SimpleGraph (Fin n)} (x y : Vtx F) :
    (Reduction.graph F).Adj x y ↔
    (col x = col y ∧ side x ≠ side y) ∨
    (row x = row y ∧ (col x + 1 = col y ∨ col y + 1 = col x)) := by
  change (ColumnGraph.graph _ _).Adj x.val y.val ↔ _
  rw [column_adj]
  simp only [row, col, side, Fin.ext_iff]

theorem bounds {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F) :
    2 * lo (row x).1 ≤ col x ∧ col x ≤ 2 * hi (row x).1 := by
  have h := x.property
  change (col x = 2 * lo (row x).1 ∧ side x = (row x).2) ∨
    (2 * lo (row x).1 < col x ∧ col x < 2 * hi (row x).1) ∨
    (col x = 2 * hi (row x).1 ∧ side x = !(row x).2) at h
  have := lo_lt_hi (row x).1
  omega

theorem side_at_lo {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F)
    (h : col x = 2 * lo (row x).1) : side x = (row x).2 := by
  have hx := x.property
  change (col x = 2 * lo (row x).1 ∧ side x = (row x).2) ∨
    (2 * lo (row x).1 < col x ∧ col x < 2 * hi (row x).1) ∨
    (col x = 2 * hi (row x).1 ∧ side x = !(row x).2) at hx
  have := lo_lt_hi (row x).1
  rcases hx with hx | hx | hx
  · exact hx.2
  · omega
  · omega

theorem side_at_hi {n : ℕ} {F : SimpleGraph (Fin n)} (x : Vtx F)
    (h : col x = 2 * hi (row x).1) : side x = !(row x).2 := by
  have hx := x.property
  change (col x = 2 * lo (row x).1 ∧ side x = (row x).2) ∨
    (2 * lo (row x).1 < col x ∧ col x < 2 * hi (row x).1) ∨
    (col x = 2 * hi (row x).1 ∧ side x = !(row x).2) at hx
  have := lo_lt_hi (row x).1
  rcases hx with hx | hx | hx
  · omega
  · omega
  · exact hx.2

theorem independent_same_column {n : ℕ} {F : SimpleGraph (Fin n)}
    {I : Finset (Vtx F)} (hI : (Reduction.graph F).IsIndepSet I)
    {x y : Vtx F} (hx : x ∈ I) (hy : y ∈ I) (hcol : col x = col y) :
    side x = side y := by
  by_contra h
  have hxy : x ≠ y := by intro heq; subst y; exact h rfl
  exact hI hx hy hxy ((adj x y).mpr (Or.inl ⟨hcol, h⟩))

theorem independent_separated {n : ℕ} {F : SimpleGraph (Fin n)}
    {I : Finset (Vtx F)} (hI : (Reduction.graph F).IsIndepSet I)
    {x y : Vtx F} (hx : x ∈ I) (hy : y ∈ I) (hrow : row x = row y) :
    col x + 1 ≠ col y := by
  intro hcol
  have hxy : x ≠ y := by intro h; subst y; omega
  exact hI hx hy hxy ((adj x y).mpr (Or.inr ⟨hrow, Or.inl hcol⟩))

theorem sum_edges {n : ℕ} (F : SimpleGraph (Fin n)) (f : Fin n × Fin n → ℕ) :
    (∑ e : Reduction.Edge F, f e.val) = ∑ e ∈ MaxCut.edges F, f e := by
  classical
  symm
  exact Finset.sum_subtype _ (fun e => by simp [MaxCut.edges]) f

theorem sum_span {n : ℕ} (F : SimpleGraph (Fin n)) :
    (∑ e : Reduction.Edge F, 2 * span e) = Reduction.offset F := by
  classical
  rw [← Finset.mul_sum, Reduction.offset]
  congr 1
  exact sum_edges F (fun e => e.2.val - e.1.val)

end Lax762056Proofs.ReductionBasics
