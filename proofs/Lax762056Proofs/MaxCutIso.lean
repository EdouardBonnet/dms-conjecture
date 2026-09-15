import Lax762056Proofs.CutScores

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.MaxCutIso

open Lax762056

attribute [local instance] Classical.propDecidable

theorem edges_card {n : ℕ} (F : SimpleGraph (Fin n)) :
    (MaxCut.edges F).card = F.edgeFinset.card := by
  classical
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · intro p hp
    have h : p.1 < p.2 ∧ F.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    simpa using h.2
  · intro p hp q hq he
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
    have hq' : q.1 < q.2 := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · rw [h₁, h₂] at hp'
      exact (lt_asymm hp' hq').elim
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hAdj : F.Adj u v := by simpa using he
      rcases lt_or_gt_of_ne hAdj.ne with h | h
      · exact ⟨(u, v), by simp [MaxCut.edges, h, hAdj], rfl⟩
      · exact ⟨(v, u), by simp [MaxCut.edges, h, hAdj.symm], Sym2.eq_swap⟩

def cutGraph {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := F.Adj x y ∧ ((x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S))
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem cutSize_card {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    MaxCut.cutSize F S = (cutGraph F S).edgeFinset.card := by
  classical
  rw [← edges_card]
  unfold MaxCut.cutSize MaxCut.edges
  congr 1
  ext p
  simp [cutGraph, and_assoc]

noncomputable def preimage {n m : ℕ} {F : SimpleGraph (Fin n)} {G : SimpleGraph (Fin m)}
    (e : F ≃g G) (S : Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => e v ∈ S)

theorem cutSize_iso {n m : ℕ} {F : SimpleGraph (Fin n)} {G : SimpleGraph (Fin m)}
    (e : F ≃g G) (S : Finset (Fin m)) :
    MaxCut.cutSize F (preimage e S) = MaxCut.cutSize G S := by
  classical
  let iso : cutGraph F (preimage e S) ≃g cutGraph G S :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro x y
        change G.Adj (e x) (e y) ∧ _ ↔ F.Adj x y ∧ _
        simp [preimage, e.map_rel_iff] }
  rw [cutSize_card, cutSize_card]
  convert iso.card_edgeFinset_eq using 1 <;>
    apply congrArg Finset.card <;> ext edge <;> simp

theorem maxCut_le {n m : ℕ} {F : SimpleGraph (Fin n)} {G : SimpleGraph (Fin m)} (e : F ≃g G) :
    MaxCut.maxCut G ≤ MaxCut.maxCut F := by
  obtain ⟨S, hS⟩ := CutScores.exists_maxCut G
  apply (CutScores.le_maxCut_iff F _).mpr
  refine ⟨preimage e S, ?_⟩
  rw [cutSize_iso, hS]

theorem maxCut_eq {n m : ℕ} {F : SimpleGraph (Fin n)} {G : SimpleGraph (Fin m)} (e : F ≃g G) :
    MaxCut.maxCut F = MaxCut.maxCut G :=
  Nat.le_antisymm (maxCut_le e.symm) (maxCut_le e)

end Lax762056Proofs.MaxCutIso
