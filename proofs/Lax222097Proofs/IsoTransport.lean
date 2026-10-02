import Lax222097Proofs.InducedModels
import Lax222097.GraphEncoding
import Lax222097.Grid

namespace Lax222097Proofs.IsoTransport

open Lax222097

variable {U V W : Type*} {G : SimpleGraph U} {G' : SimpleGraph V} {H : SimpleGraph W}

/-- Transport an induced-minor model along an isomorphism of its host graph. -/
def mapModel (e : G ≃g G') (M : InducedMinors.Model H G) : InducedMinors.Model H G' where
  branch v := e '' M.branch v
  connected v := by
    let f : G.induce (M.branch v) →g G'.induce (e '' M.branch v) :=
      { toFun := fun x => ⟨e x.val, ⟨x.val, x.property, rfl⟩⟩
        map_rel' := fun h => e.map_rel_iff.mpr h }
    apply (M.connected v).map f
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  disjoint u v huv := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have he : b = a := e.injective hba
    subst b
    exact Set.disjoint_left.mp (M.disjoint u v huv) ha hb
  adjacent u v huv := by
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, hab⟩ := (M.adjacent u v huv).mp h
      exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, e.map_rel_iff.mpr hab⟩
    · rintro ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, hab⟩
      exact (M.adjacent u v huv).mpr ⟨a, ha, b, hb, e.map_rel_iff.mp hab⟩

theorem excludes_inducedGrid {k : ℕ} (e : G ≃g G')
    (h : Grid.ExcludesInducedGrid k G') : Grid.ExcludesInducedGrid k G := by
  rintro ⟨M⟩
  exact h ⟨mapModel e M⟩

theorem indepNum_le [Finite V] (e : G ≃g G') : G.indepNum ≤ G'.indepNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hi : G'.IsIndepSet (s.image e) := by
    rintro x hx y hy hxy hAdj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hs.isIndepSet ha hb (fun hab => hxy (congrArg e hab)) (e.map_rel_iff.mp hAdj)
  have hc := hi.card_le_indepNum
  rw [Finset.card_image_of_injective _ e.injective, hs.card_eq] at hc
  exact hc

theorem indepNum_eq [Finite U] [Finite V] (e : G ≃g G') : G.indepNum = G'.indepNum :=
  Nat.le_antisymm (indepNum_le e) (indepNum_le e.symm)

end Lax222097Proofs.IsoTransport
