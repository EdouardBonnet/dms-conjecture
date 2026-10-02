import Lax222097Proofs.ThreeSAT
import Lax222097Proofs.SubdividedLabels
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ProdSigma

namespace Lax222097Proofs.CutVertices

abbrev Variable (n : ℕ) := (Bool × Fin n) ⊕ Unit
abbrev Occurrence (n : ℕ) := Variable n ⊕ (Fin n × Bool × Fin 3)
abbrev Point (n : ℕ) := (Variable n × Bool) ⊕ (Occurrence n × Bool)

def variableNumber {n : ℕ} : Variable n → Fin (n + 1 + n)
  | .inl (false, v) => ThreeSAT.old n v
  | .inl (true, v) => ThreeSAT.auxiliary n v
  | .inr _ => ThreeSAT.anchor n n

def unvariable {n : ℕ} (v : Fin (n + 1 + n)) : Variable n :=
  if h : v.val < n then .inl (false, ⟨v.val, h⟩)
  else if he : v.val = n then .inr ()
  else .inl (true, ⟨v.val - (n + 1), by omega⟩)

def variableEquiv (n : ℕ) : Variable n ≃ Fin (n + 1 + n) where
  toFun := variableNumber
  invFun := unvariable
  left_inv := by
    rintro (⟨b, v⟩ | u)
    · cases b
      · simp [variableNumber, unvariable, ThreeSAT.old]
      · have h₁ : ¬ n + 1 + v.val < n := by omega
        have h₂ : n + 1 + v.val ≠ n := by omega
        simp [variableNumber, unvariable, ThreeSAT.auxiliary, h₁, h₂]
    · cases u; simp [variableNumber, unvariable, ThreeSAT.anchor]
  right_inv := by
    intro v
    unfold unvariable
    split
    · rfl
    · split
      · apply Fin.ext; simpa [variableNumber, ThreeSAT.anchor] using (by assumption : v.val = n).symm
      · apply Fin.ext
        simp only [variableNumber, ThreeSAT.auxiliary]
        omega

def bitEquiv (n : ℕ) : Fin n × Bool ≃ Fin (2 * n) where
  toFun := NAEMaxCut.index
  invFun v := (⟨v.val / 2, by omega⟩, decide (v.val % 2 = 1))
  left_inv := by rintro ⟨v, b⟩; cases b <;> simp [NAEMaxCut.index, Nat.add_div]
  right_inv := by
    intro v
    apply Fin.ext
    simp only [NAEMaxCut.index]
    split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> omega

def coreEquiv (n : ℕ) : Variable n × Bool ≃ Fin (2 * (n + 1 + n)) :=
  (Equiv.prodCongr (variableEquiv n) (Equiv.refl Bool)).trans (bitEquiv _)

def clauseEquiv (n : ℕ) : (Fin n × Bool × Fin 3) ≃ (Fin (n * 2) × Fin 3) :=
  (Equiv.prodAssoc (Fin n) Bool (Fin 3)).symm.trans
    (Equiv.prodCongr ((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv)
      (Equiv.refl (Fin 3)))

def occurrenceEquiv (n : ℕ) : Occurrence n ≃ Fin (n + 1 + n + (n * 2) * 3) :=
  (Equiv.sumCongr (variableEquiv n) (clauseEquiv n)).trans (NAEMaxCut.edgeEquiv _ _)

def order (n : ℕ) := 2 * (n + 1 + n) + 2 * (n + 1 + n + (n * 2) * 3)

def pointEquiv (n : ℕ) : Point n ≃ Fin (order n) :=
  (Equiv.sumCongr (coreEquiv n) (Equiv.prodCongr (occurrenceEquiv n) (Equiv.refl Bool))).trans
    (SubdividedLabels.equiv _ _)

inductive VarTag
  | core (aux sign : Bool)
  | variablePath (aux side : Bool)
  | clausePath (second : Bool) (edge : Fin 3) (side : Bool)
  deriving DecidableEq, Fintype

inductive ConstTag
  | core (sign : Bool)
  | variablePath (side : Bool)
  deriving DecidableEq, Fintype

abbrev Raw (n : ℕ) := (VarTag × Fin n) ⊕ ConstTag

def rawEquiv (n : ℕ) : Raw n ≃ Point n where
  toFun
    | .inl (.core aux sign, v) => .inl (.inl (aux, v), sign)
    | .inl (.variablePath aux side, v) => .inr (.inl (.inl (aux, v)), side)
    | .inl (.clausePath second edge side, v) => .inr (.inr (v, second, edge), side)
    | .inr (.core sign) => .inl (.inr (), sign)
    | .inr (.variablePath side) => .inr (.inl (.inr ()), side)
  invFun
    | .inl (.inl (aux, v), sign) => .inl (.core aux sign, v)
    | .inl (.inr _, sign) => .inr (.core sign)
    | .inr (.inl (.inl (aux, v)), side) => .inl (.variablePath aux side, v)
    | .inr (.inl (.inr _), side) => .inr (.variablePath side)
    | .inr (.inr (v, second, edge), side) => .inl (.clausePath second edge side, v)
  left_inv := by
    rintro (⟨tag, v⟩ | tag) <;> cases tag <;> rfl
  right_inv := by
    rintro (⟨(⟨aux, v⟩ | u), sign⟩ | ⟨(⟨(⟨aux, v⟩ | u)⟩ | ⟨v, second, edge⟩), side⟩) <;>
      first | rfl | cases u; rfl

def rawFinEquiv (n : ℕ) : Raw n ≃ Fin (order n) := (rawEquiv n).trans (pointEquiv n)

def tags : List VarTag :=
  [false, true].flatMap (fun aux => [false, true].map (.core aux)) ++
    [false, true].flatMap (fun aux => [false, true].map (.variablePath aux)) ++
      [false, true].flatMap (fun second => (List.finRange 3).flatMap (fun edge =>
        [false, true].map (.clausePath second edge)))

def constants : List ConstTag := [.core false, .core true, .variablePath false, .variablePath true]

def labels (n : ℕ) : List (Raw n) :=
  ((tags.product (List.finRange n)).map Sum.inl) ++ constants.map Sum.inr

theorem tags_nodup : tags.Nodup := by decide
theorem constants_nodup : constants.Nodup := by decide
theorem tags_length : tags.length = 20 := by decide
theorem constants_length : constants.length = 4 := by decide

theorem mem_tags (t : VarTag) : t ∈ tags := by
  cases t with
  | core a s => cases a <;> cases s <;> decide
  | variablePath a s => cases a <;> cases s <;> decide
  | clausePath a e s => cases a <;> cases s <;> fin_cases e <;> decide

theorem mem_constants (t : ConstTag) : t ∈ constants := by
  cases t <;> rename_i b <;> cases b <;> decide

theorem labels_nodup (n : ℕ) : (labels n).Nodup := by
  rw [labels, List.nodup_append]
  refine ⟨(tags_nodup.product (List.nodup_finRange n)).map Sum.inl_injective,
    constants_nodup.map Sum.inr_injective, ?_⟩
  simp [List.disjoint_left]

theorem mem_labels {n : ℕ} (x : Raw n) : x ∈ labels n := by
  rcases x with ⟨t, v⟩ | t
  · simp [labels, mem_tags]
  · simp [labels, mem_constants]

theorem labels_length (n : ℕ) : (labels n).length = 20 * n + 4 := by
  simp only [labels, List.length_append, List.length_map]
  rw [show (tags.product (List.finRange n)).length = tags.length * (List.finRange n).length from
    List.length_product tags (List.finRange n)]
  simp [tags_length, constants_length]

noncomputable def labelEquiv (n : ℕ) : Fin (labels n).length ≃ Fin (order n) :=
  (List.Nodup.getEquivOfForallMemList (labels n) (labels_nodup n) mem_labels).trans (rawFinEquiv n)

end Lax222097Proofs.CutVertices
