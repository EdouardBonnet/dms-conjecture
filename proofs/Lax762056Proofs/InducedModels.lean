import Lax762056.InducedMinors
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic

namespace Lax762056Proofs.InducedModels

open Lax762056.InducedMinors

variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}

def union (M : Model H G) (S : Set W) : Set V :=
  {x | ∃ v ∈ S, x ∈ M.branch v}

theorem branch_subset (M : Model H G) {S : Set W} {v : W} (hv : v ∈ S) :
    M.branch v ⊆ union M S := fun _ hx => ⟨v, hv, hx⟩

theorem branch_reachable (M : Model H G) {S : Set W} {v : W} (hv : v ∈ S)
    (x y : union M S) (hx : x.val ∈ M.branch v) (hy : y.val ∈ M.branch v) :
    (G.induce (union M S)).Reachable x y := by
  let f : (G.induce (M.branch v)) →g (G.induce (union M S)) :=
    { toFun := fun z => ⟨z.val, ⟨v, hv, z.property⟩⟩
      map_rel' := fun h => h }
  exact ((M.connected v) ⟨x.val, hx⟩ ⟨y.val, hy⟩).map f

theorem walk_reachable (M : Model H G) {S : Set W} {u v : W}
    (p : H.Walk u v) (hp : ∀ z ∈ p.support, z ∈ S)
    (x y : union M S) (hx : x.val ∈ M.branch u) (hy : y.val ∈ M.branch v) :
    (G.induce (union M S)).Reachable x y := by
  induction p generalizing x with
  | nil => exact branch_reachable M (hp _ (by simp)) x y hx hy
  | @cons u v w huv p ih =>
    have hu : u ∈ S := hp _ (by simp)
    have hv : v ∈ S := hp _ (by simp)
    obtain ⟨a, ha, b, hb, hab⟩ := (M.adjacent u v huv.ne).mp huv
    let aa : union M S := ⟨a, ⟨u, hu, ha⟩⟩
    let bb : union M S := ⟨b, ⟨v, hv, hb⟩⟩
    have hxa := branch_reachable M hu x aa hx ha
    have hab' : (G.induce (union M S)).Reachable aa bb := SimpleGraph.Adj.reachable hab
    have hby := ih (fun z hz => hp z (by simpa using Or.inr hz)) bb hb hy
    exact hxa.trans (hab'.trans hby)

theorem union_connected (M : Model H G) {S : Set W} (hS : (H.induce S).Connected) :
    (G.induce (union M S)).Connected := by
  have hne : Nonempty (union M S) := by
    obtain ⟨v⟩ := hS.nonempty
    obtain ⟨x⟩ := (M.connected v.val).nonempty
    exact ⟨⟨x.val, v.val, v.property, x.property⟩⟩
  letI := hne
  constructor
  intro x y
  obtain ⟨u, hu, hx⟩ := x.property
  obtain ⟨v, hv, hy⟩ := y.property
  obtain ⟨p⟩ := hS ⟨u, hu⟩ ⟨v, hv⟩
  let f : H.induce S →g H := { toFun := Subtype.val, map_rel' := fun h => h }
  have hp : ∀ z ∈ (p.map f).support, z ∈ S := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact a.property
  exact walk_reachable M (p.map f) hp x y hx hy

def liftInduce {S : Set V} (M : Model H (G.induce S)) : Model H G where
  branch v := Subtype.val '' M.branch v
  connected v := by
    let f : ((G.induce S).induce (M.branch v)) →g
        G.induce (Subtype.val '' M.branch v) :=
      { toFun := fun x => ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩
        map_rel' := fun h => h }
    apply (M.connected v).map f
    rintro ⟨x, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  disjoint u v huv := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    exact Set.disjoint_left.mp (M.disjoint u v huv) (hab ▸ ha) hb
  adjacent u v huv := by
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, hab⟩ := (M.adjacent u v huv).mp h
      exact ⟨a.val, ⟨a, ha, rfl⟩, b.val, ⟨b, hb, rfl⟩, hab⟩
    · rintro ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, hab⟩
      exact (M.adjacent u v huv).mpr ⟨a, ha, b, hb, hab⟩

end Lax762056Proofs.InducedModels
