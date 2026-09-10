import Mathlib.Tactic

namespace Lax762056Proofs.Counting

/-- Pair consecutive integer positions. A set with no consecutive elements
occupies each pair at most once. -/
theorem card_le_of_separated (S : Finset ℕ) (a d : ℕ)
    (hbound : ∀ x ∈ S, a ≤ x ∧ x < a + 2 * d)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x + 1 ≠ y) : S.card ≤ d := by
  have hinj : Set.InjOn (fun x => (x - a) / 2) (S : Set ℕ) := by
    intro x hx y hy hxy
    change (x - a) / 2 = (y - a) / 2 at hxy
    have hbx := hbound x hx
    have hby := hbound y hy
    have h1 := hsep x hx y hy
    have h2 := hsep y hy x hx
    omega
  calc
    S.card = (S.image fun x => (x - a) / 2).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range d).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have := hbound x hx
      simp only [Finset.mem_range]
      omega
    _ = d := Finset.card_range d

/-- A row with `2*d+1` positions contributes at most `d+1` vertices.
Reaching `d+1` forces both endpoints to be selected. -/
theorem row_bound (S : Finset ℕ) (a d : ℕ)
    (hbound : ∀ x ∈ S, a ≤ x ∧ x ≤ a + 2 * d)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x + 1 ≠ y) :
    S.card ≤ d + 1 ∧ (d < S.card → a ∈ S ∧ a + 2 * d ∈ S) := by
  constructor
  · apply card_le_of_separated S a (d + 1) _ hsep
    intro x hx
    have := hbound x hx
    omega
  · intro hlarge
    constructor
    · by_contra ha
      have hsmall := card_le_of_separated S (a + 1) d (by
        intro x hx
        have := hbound x hx
        have : x ≠ a := by intro h; subst x; exact ha hx
        omega) hsep
      omega
    · by_contra ha
      have hsmall := card_le_of_separated S a d (by
        intro x hx
        have := hbound x hx
        have : x ≠ a + 2 * d := by intro h; subst x; exact ha hx
        omega) hsep
      omega

end Lax762056Proofs.Counting
