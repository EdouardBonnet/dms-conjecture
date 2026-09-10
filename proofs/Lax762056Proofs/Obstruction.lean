import Lax762056.CycleObstruction
import Lax762056Proofs.CyclePairs

namespace Lax762056Proofs.Obstruction

open Lax762056 ColumnSets InducedModels

def Separated {V : Type*} (G : SimpleGraph V) (S T : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y

theorem union_separated {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : InducedMinors.Model H G) {S T : Set W} (h : Separated H S T) :
    Separated G (union M S) (union M T) := by
  rintro x ⟨u, hu, hx⟩ y ⟨v, hv, hy⟩
  have huv := h u hu v hv
  constructor
  · intro hxy
    exact Set.disjoint_left.mp (M.disjoint u v huv.1) (hxy ▸ hx) hy
  · intro hxy
    exact huv.2 ((M.adjacent u v huv.1).mpr ⟨x, hx, y, hy, hxy⟩)

theorem avoids_column {R : Type*} {c : ℕ}
    {S T : Set (ColumnGraph.Vertex R c)}
    (hsep : Separated (ColumnGraph.graph R c) S T)
    {a b : ColumnGraph.Vertex R c} (ha : a ∈ T) (hb : b ∈ T)
    (hab : column a = column b) (hside : a.2.2 ≠ b.2.2)
    {x : ColumnGraph.Vertex R c} (hx : x ∈ S) : column x ≠ column a := by
  intro hcol
  have hxa : x.2.2 = a.2.2 := by
    by_contra hne
    exact (hsep x hx a ha).2 ((ReductionBasics.column_adj x a).mpr
      (Or.inl ⟨Fin.ext hcol, hne⟩))
  have hxb : x.2.2 = b.2.2 := by
    by_contra hne
    exact (hsep x hx b hb).2 ((ReductionBasics.column_adj x b).mpr
      (Or.inl ⟨Fin.ext (hcol.trans hab), hne⟩))
  exact hside (hxa.symm.trans hxb)

theorem connected_left {R : Type*} {c k : ℕ} {S : Set (ColumnGraph.Vertex R c)}
    (hS : ((ColumnGraph.graph R c).induce S).Connected)
    (hno : ∀ z ∈ S, column z ≠ k)
    {x : ColumnGraph.Vertex R c} (hx : x ∈ S) (hxl : column x < k) :
    ∀ y ∈ S, column y < k := by
  intro y hy
  by_contra hyl
  obtain ⟨z, hz, hzk⟩ := connected_hits hS hx hy k (by omega) (by omega)
  exact hno z hz hzk

theorem connected_right {R : Type*} {c k : ℕ} {S : Set (ColumnGraph.Vertex R c)}
    (hS : ((ColumnGraph.graph R c).induce S).Connected)
    (hno : ∀ z ∈ S, column z ≠ k)
    {x : ColumnGraph.Vertex R c} (hx : x ∈ S) (hxl : k < column x) :
    ∀ y ∈ S, k < column y := by
  intro y hy
  by_contra hyl
  obtain ⟨z, hz, hzk⟩ := connected_hits hS hy hx k (by omega) (by omega)
  exact hno z hz hzk

theorem order_three (f : Fin 3 → ℕ)
    (h : ∀ i j, i ≠ j → f i ≠ f j) :
    ∃ a b d, f a < f b ∧ f b < f d := by
  have h01 := h 0 1 (by decide)
  have h02 := h 0 2 (by decide)
  have h12 := h 1 2 (by decide)
  by_cases hlt01 : f 0 < f 1 <;> by_cases hlt02 : f 0 < f 2 <;>
    by_cases hlt12 : f 1 < f 2 <;>
    first
    | exact ⟨0, 1, 2, by omega, by omega⟩
    | exact ⟨0, 2, 1, by omega, by omega⟩
    | exact ⟨1, 0, 2, by omega, by omega⟩
    | exact ⟨1, 2, 0, by omega, by omega⟩
    | exact ⟨2, 0, 1, by omega, by omega⟩
    | exact ⟨2, 1, 0, by omega, by omega⟩

/--
---
conclusion: Lax762056.CycleObstruction.avoidingCycles_obstruction
---
Each cycle's branch sets contain opposite sides of a column. The three
columns are distinct. The middle column is contained in the middle cycle's
closed neighborhood and separates the other two cycles, contradicting their
avoiding path.
-/
theorem avoidingCycles_obstruction (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : AsteroidalCycles.HasAsteroidalTriple H) :
    ¬ InducedMinors.IsInducedMinor H (ColumnGraph.graph R c) := by
  classical
  rintro ⟨M⟩
  obtain ⟨base, cycle, hcycle, hsep, hpaths⟩ := hH
  let U (i : Fin 3) := union M {w | w ∈ (cycle i).support}
  have hUc (i) : ((ColumnGraph.graph R c).induce (U i)).Connected :=
    union_connected M (cycle i).connected_induce_support
  have hUs (i j) (hij : i ≠ j) : Separated (ColumnGraph.graph R c) (U i) (U j) :=
    union_separated M (hsep hij)
  have hpairs (i) : ∃ x ∈ U i, ∃ y ∈ U i,
      column x = column y ∧ x.2.2 ≠ y.2.2 :=
    CyclePairs.cycle_pair M (cycle i) (hcycle i)
  choose x hx y hy hcol hside using hpairs
  have hdistinct (i j) (hij : i ≠ j) : column (x i) ≠ column (x j) :=
    avoids_column (hUs i j hij) (hx j) (hy j) (hcol j) (hside j) (hx i)
  obtain ⟨a, b, d, hab, hbd⟩ := order_three (fun i => column (x i)) hdistinct
  have hab' : a ≠ b := by intro he; subst b; omega
  have had' : a ≠ d := by intro he; subst d; omega
  have hbd' : b ≠ d := by intro he; subst d; omega
  have hnoa : ∀ z ∈ U a, column z ≠ column (x b) :=
    fun z hz => avoids_column (hUs a b hab') (hx b) (hy b) (hcol b) (hside b) hz
  have hnod : ∀ z ∈ U d, column z ≠ column (x b) :=
    fun z hz => avoids_column (hUs d b hbd'.symm) (hx b) (hy b) (hcol b) (hside b) hz
  have hleft := connected_left (hUc a) hnoa (hx a) hab
  have hright := connected_right (hUc d) hnod (hx d) hbd
  obtain ⟨u, hu, v, hv, p, hp⟩ := hpaths a d b had' hab' hbd'.symm
  rcases p with ⟨p, _⟩
  let P := union M {w | w ∈ p.support}
  have hPc : ((ColumnGraph.graph R c).induce P).Connected :=
    union_connected M p.connected_induce_support
  have hPs : Separated (ColumnGraph.graph R c) P (U b) := union_separated M hp
  have hnoP : ∀ z ∈ P, column z ≠ column (x b) :=
    fun z hz => avoids_column hPs (hx b) (hy b) (hcol b) (hside b) hz
  obtain ⟨z⟩ := (M.connected u).nonempty
  obtain ⟨w⟩ := (M.connected v).nonempty
  have hzP : z.val ∈ P := ⟨u, p.start_mem_support, z.property⟩
  have hwP : w.val ∈ P := ⟨v, p.end_mem_support, w.property⟩
  have hzleft := hleft z.val ⟨u, hu, z.property⟩
  have hwright := hright w.val ⟨v, hv, w.property⟩
  obtain ⟨t, ht, htc⟩ := connected_hits hPc hzP hwP (column (x b)) (by omega) (by omega)
  exact hnoP t ht htc

end Lax762056Proofs.Obstruction
