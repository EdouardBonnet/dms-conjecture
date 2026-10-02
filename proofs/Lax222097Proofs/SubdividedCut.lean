import Lax222097Proofs.CutScores

/-! Replace every edge occurrence of a multigraph by a path with two fresh
internal vertices. This produces a simple unweighted graph even when an
occurrence is a loop or several occurrences have the same endpoints. -/

namespace Lax222097Proofs.SubdividedCut

open Lax222097 CutScores

variable {n m : ℕ}

def core (m : ℕ) (v : Fin n) : Fin (n + 2 * m) := ⟨v.val, by omega⟩

def middle (n : ℕ) (e : Fin m) (b : Bool) : Fin (n + 2 * m) :=
  ⟨n + 2 * e.val + (if b then 1 else 0), by cases b <;> simp <;> omega⟩

def edgePair (l r : Fin m → Fin n) (p : Fin m × Fin 3) :
    Fin (n + 2 * m) × Fin (n + 2 * m) :=
  if p.2 = 0 then (core m (l p.1), middle n p.1 false)
  else if p.2 = 1 then (middle n p.1 false, middle n p.1 true)
  else (core m (r p.1), middle n p.1 true)

theorem edgePair_lt (l r : Fin m → Fin n) (p : Fin m × Fin 3) :
    (edgePair l r p).1 < (edgePair l r p).2 := by
  rcases p with ⟨e, k⟩
  fin_cases k <;> simp [edgePair, core, middle, Fin.lt_def] <;> omega

theorem edgePair_injective (l r : Fin m → Fin n) : Function.Injective (edgePair l r) := by
  rintro ⟨e, k⟩ ⟨f, j⟩ h
  have h₁ := congrArg (fun x => x.1.val) h
  have h₂ := congrArg (fun x => x.2.val) h
  fin_cases k <;> fin_cases j <;> simp [edgePair, core, middle] at h₁ h₂
  all_goals simp only [Prod.mk.injEq, Fin.ext_iff]
  all_goals first | exact ⟨h₂, trivial⟩ | omega

def graph (l r : Fin m → Fin n) : SimpleGraph (Fin (n + 2 * m)) :=
  SimpleGraph.fromRel (fun x y => ∃ p, (x, y) = edgePair l r p)

theorem edges_graph (l r : Fin m → Fin n) :
    MaxCut.edges (graph l r) = Finset.univ.image (edgePair l r) := by
  classical
  ext xy
  rcases xy with ⟨x, y⟩
  simp only [MaxCut.edges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hxy, hAdj⟩
    rw [graph, SimpleGraph.fromRel_adj] at hAdj
    rcases hAdj.2 with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp.symm⟩
    · have hlt := edgePair_lt l r p
      rw [← hp] at hlt
      exact (lt_asymm hxy hlt).elim
  · rintro ⟨p, hp⟩
    have hlt := edgePair_lt l r p
    have he : edgePair l r p = (x, y) := hp
    rw [he] at hlt
    refine ⟨hlt, ?_⟩
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨ne_of_lt hlt, Or.inl ⟨p, he.symm⟩⟩

noncomputable def score (l r : Fin m → Fin n) (ρ : Fin n → Bool) : ℕ :=
  ∑ e : Fin m, apart (ρ (l e)) (ρ (r e))

theorem cutSize_graph (l r : Fin m → Fin n) (S : Finset (Fin (n + 2 * m))) :
    MaxCut.cutSize (graph l r) S =
      ∑ e : Fin m,
        (apart (decide (core m (l e) ∈ S)) (decide (middle n e false ∈ S)) +
          apart (decide (middle n e false ∈ S)) (decide (middle n e true ∈ S)) +
          apart (decide (middle n e true ∈ S)) (decide (core m (r e) ∈ S))) := by
  classical
  rw [cutSize_eq_sum, edges_graph, Finset.sum_image]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e he
    simp [Fin.sum_univ_three, edgePair, apart_symm, Nat.add_assoc]
  · exact fun _ _ _ _ h => edgePair_injective l r h

theorem cutSize_upper (l r : Fin m → Fin n) (S : Finset (Fin (n + 2 * m))) :
    MaxCut.cutSize (graph l r) S ≤ 2 * m + score l r (fun v => decide (core m v ∈ S)) := by
  classical
  rw [cutSize_graph]
  calc
    _ ≤ ∑ e : Fin m, (2 + apart (decide (core m (l e) ∈ S))
        (decide (core m (r e) ∈ S))) := Finset.sum_le_sum (fun _ _ => path_bound _ _ _ _)
    _ = _ := by simp [Finset.sum_add_distrib, score, Nat.mul_comm]

def extend (l : Fin m → Fin n) (ρ : Fin n → Bool) (v : Fin (n + 2 * m)) : Bool :=
  if hv : v.val < n then ρ ⟨v.val, hv⟩
  else
    let e : Fin m := ⟨(v.val - n) / 2, by omega⟩
    if (v.val - n) % 2 = 0 then !ρ (l e) else ρ (l e)

theorem extend_core (l : Fin m → Fin n) (ρ : Fin n → Bool) (v : Fin n) :
    extend l ρ (core m v) = ρ v := by simp [extend, core]

theorem extend_middle_false (l : Fin m → Fin n) (ρ : Fin n → Bool) (e : Fin m) :
    extend l ρ (middle n e false) = !ρ (l e) := by
  have hnot : ¬ (middle n e false).val < n := by simp [middle]
  have hdiv : ((middle n e false).val - n) / 2 = e.val := by simp [middle]
  have hmod : ((middle n e false).val - n) % 2 = 0 := by simp [middle]
  simp [extend, hnot, hdiv, hmod]

theorem extend_middle_true (l : Fin m → Fin n) (ρ : Fin n → Bool) (e : Fin m) :
    extend l ρ (middle n e true) = ρ (l e) := by
  have hnot : ¬ (middle n e true).val < n := by simp [middle]; omega
  have hdiv : ((middle n e true).val - n) / 2 = e.val := by simp [middle]; omega
  have hmod : ((middle n e true).val - n) % 2 ≠ 0 := by simp [middle]; omega
  simp [extend, hnot, hdiv, hmod]

theorem cutSize_attains (l r : Fin m → Fin n) (ρ : Fin n → Bool) :
    MaxCut.cutSize (graph l r) (cutSet (extend l ρ)) = 2 * m + score l r ρ := by
  rw [cutSize_graph]
  simp only [decide_mem_cutSet, extend_core, extend_middle_false, extend_middle_true,
    path_attains]
  simp [Finset.sum_add_distrib, score, Nat.mul_comm]

/-- Every cut of the original edge occurrences extends optimally, and every
cut of the simple graph loses at most the fixed two-per-occurrence offset. -/
theorem reduction_iff (l r : Fin m → Fin n) (k : ℕ) :
    2 * m + k ≤ MaxCut.maxCut (graph l r) ↔ ∃ ρ : Fin n → Bool, k ≤ score l r ρ := by
  classical
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (le_maxCut_iff (graph l r) (2 * m + k)).mp h
    have hu := cutSize_upper l r S
    exact ⟨fun v => decide (core m v ∈ S), by omega⟩
  · rintro ⟨ρ, hρ⟩
    apply (le_maxCut_iff (graph l r) (2 * m + k)).mpr
    refine ⟨cutSet (extend l ρ), ?_⟩
    rw [cutSize_attains]
    omega

end Lax222097Proofs.SubdividedCut
