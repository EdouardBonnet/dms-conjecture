import Lax762056Proofs.CutVertices

namespace Lax762056Proofs.CutEndpoints

open CutVertices

def original {n : ℕ} (l : NAEMaxCut.Literal n) : Variable n × Bool := (.inl (false, l.1), l.2)

def clauseLiteral {n : ℕ} (C : NAEMaxCut.Formula n n) (i : Fin n) (second : Bool)
    (j : Fin 3) : Variable n × Bool :=
  if second then
    if j = 0 then (.inl (true, i), false)
    else if j = 1 then original (C i 2) else (.inr (), true)
  else
    if j = 0 then original (C i 0)
    else if j = 1 then original (C i 1) else (.inl (true, i), true)

def slot (edge : Fin 3) (side : Bool) : Fin 3 :=
  if edge = 0 then if side then 1 else 0
  else if edge = 1 then if side then 2 else 1
  else if side then 2 else 0

def endpoint {n : ℕ} (C : NAEMaxCut.Formula n n) : Occurrence n → Bool → Variable n × Bool
  | .inl v, side => (v, side)
  | .inr (i, second, edge), side => clauseLiteral C i second (slot edge side)

theorem clauseLiteral_index {n : ℕ} (C : NAEMaxCut.Formula n n) (i : Fin n) (b : Bool) (j : Fin 3) :
    coreEquiv n (clauseLiteral C i b j) =
      NAEMaxCut.index (ThreeSAT.toNAE C (finProdFinEquiv (i, finTwoEquiv.symm b)) j) := by
  cases b <;> fin_cases j <;>
    simp [clauseLiteral, original, coreEquiv, bitEquiv, variableEquiv, variableNumber,
      ThreeSAT.toNAE, ThreeSAT.oldLiteral, finTwoEquiv]

theorem endpoint_index {n : ℕ} (C : NAEMaxCut.Formula n n) (e : Occurrence n) (b : Bool) :
    coreEquiv n (endpoint C e b) =
      if b then NAEMaxCut.right (ThreeSAT.toNAE C) (occurrenceEquiv n e)
      else NAEMaxCut.left (ThreeSAT.toNAE C) (occurrenceEquiv n e) := by
  rcases e with v | ⟨i, second, edge⟩
  · cases b <;> simp [endpoint, NAEMaxCut.left, NAEMaxCut.right, occurrenceEquiv,
      NAEMaxCut.pair, coreEquiv, bitEquiv]
  · cases b <;> fin_cases edge <;>
      simp [endpoint, slot, clauseLiteral_index, occurrenceEquiv, clauseEquiv,
        NAEMaxCut.left, NAEMaxCut.right, NAEMaxCut.pair]

def adjacent {n : ℕ} (C : NAEMaxCut.Formula n n) : Point n → Point n → Prop
  | .inl _, .inl _ => False
  | .inl x, .inr (e, b) => x = endpoint C e b
  | .inr (e, b), .inl x => x = endpoint C e b
  | .inr (e, b), .inr (f, d) => e = f ∧ b ≠ d

theorem core_core {n : ℕ} (C : NAEMaxCut.Formula n n) (x y : Variable n × Bool) :
    ¬ (ThreeSAT.toMaxCut C).graph.Adj (pointEquiv n (.inl x)) (pointEquiv n (.inl y)) :=
  SubdividedLabels.core_core _ _ _ _

theorem core_middle {n : ℕ} (C : NAEMaxCut.Formula n n) (x : Variable n × Bool)
    (e : Occurrence n) (b : Bool) :
    (ThreeSAT.toMaxCut C).graph.Adj (pointEquiv n (.inl x)) (pointEquiv n (.inr (e, b))) ↔
      x = endpoint C e b := by
  change (SubdividedCut.graph (NAEMaxCut.left (ThreeSAT.toNAE C)) (NAEMaxCut.right (ThreeSAT.toNAE C))).Adj
    (SubdividedCut.core _ (coreEquiv n x)) (SubdividedCut.middle _ (occurrenceEquiv n e) b) ↔ _
  rw [SubdividedLabels.core_middle, ← endpoint_index]
  exact (coreEquiv n).injective.eq_iff

theorem adjacent_correct {n : ℕ} (C : NAEMaxCut.Formula n n) (x y : Point n) :
    (ThreeSAT.toMaxCut C).graph.Adj (pointEquiv n x) (pointEquiv n y) ↔ adjacent C x y := by
  rcases x with x | ⟨e, b⟩ <;> rcases y with y | ⟨f, d⟩
  · exact iff_false_intro (core_core C x y)
  · exact core_middle C x f d
  · rw [SimpleGraph.adj_comm]
    exact core_middle C y e b
  · change (SubdividedCut.graph (NAEMaxCut.left (ThreeSAT.toNAE C)) (NAEMaxCut.right (ThreeSAT.toNAE C))).Adj
      (SubdividedCut.middle _ (occurrenceEquiv n e) b) (SubdividedCut.middle _ (occurrenceEquiv n f) d) ↔ _
    rw [SubdividedLabels.middle_middle]
    exact and_congr (occurrenceEquiv n).injective.eq_iff Iff.rfl

end Lax762056Proofs.CutEndpoints
