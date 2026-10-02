import Lax222097Proofs.EncodedReduction
import Lax222097Proofs.QueryCompiler.StructureEncoding

namespace Lax222097Proofs.EncodingFacts

open Lax222097 GraphEncoding

theorem encode_length (I : Instance) :
    (encode I).length = I.order ^ 2 + I.order + I.threshold + 2 := by
  classical
  simp [encode, unary, List.length_flatMap, List.sum_replicate, pow_two]
  omega

theorem encode_injective : Function.Injective encode := by
  classical
  rintro ⟨n, F, k⟩ ⟨m, G, j⟩ h
  change (unary n ++ _) ++ _ = (unary m ++ _) ++ _ at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hn, hrest⟩ := Lax222097Proofs.QueryCompiler.StructureEncoding.unary_append_inj n m _ _ h
  cases hn
  obtain ⟨hrows, hk⟩ := Lax222097Proofs.QueryCompiler.StructureEncoding.blocks_append_inj (List.finRange n)
    (fun u => (List.finRange n).map (fun v => decide (F.Adj u v)))
    (fun u => (List.finRange n).map (fun v => decide (G.Adj u v)))
    (unary k) (unary j) (by simp) hrest
  have hFG : F = G := by
    ext u v
    have hb := List.map_inj_left.mp (hrows u (by simp)) v (by simp)
    by_cases hF : F.Adj u v <;> by_cases hG : G.Adj u v <;> simp_all
  have hkj : k = j := by
    have hl := congrArg List.length hk
    simp [unary] at hl
    exact hl
  cases hFG
  cases hkj
  rfl

theorem edges_card_le {n : ℕ} (F : SimpleGraph (Fin n)) : (MaxCut.edges F).card ≤ n ^ 2 := by
  classical
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n × Fin n)))
    (p := fun e => e.1 < e.2 ∧ F.Adj e.1 e.2)
  simpa [MaxCut.edges, pow_two] using h

theorem offset_le {n : ℕ} (F : SimpleGraph (Fin n)) : Reduction.offset F ≤ 2 * n ^ 3 := by
  classical
  have hsum : (∑ e ∈ MaxCut.edges F, (e.2.val - e.1.val)) ≤ (MaxCut.edges F).card * n := by
    calc
      _ ≤ ∑ _ ∈ MaxCut.edges F, n := Finset.sum_le_sum (fun e _ => by omega)
      _ = _ := by simp
  have hc := edges_card_le F
  have hm := Nat.mul_le_mul_right n hc
  unfold Reduction.offset
  nlinarith [hsum, hm]

noncomputable def outputBound : Polynomial ℕ :=
  (8 * Polynomial.X ^ 3) ^ 2 + 10 * Polynomial.X ^ 3 + Polynomial.X + 2

theorem reduction_output_bound (I : Instance) :
    (encode (EncodedReduction.reduce I)).length ≤ outputBound.eval (encode I).length := by
  have hn : I.order ≤ (encode I).length := by rw [encode_length]; omega
  have hk : I.threshold ≤ (encode I).length := by rw [encode_length]; omega
  have hp : I.order ^ 3 ≤ (encode I).length ^ 3 := Nat.pow_le_pow_left hn 3
  have ho := (EncodedReduction.order_le I).trans (Nat.mul_le_mul_left 8 hp)
  have hb := (offset_le I.graph).trans (Nat.mul_le_mul_left 2 hp)
  have hs := Nat.mul_self_le_mul_self ho
  rw [encode_length, EncodedReduction.threshold]
  simp only [outputBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  nlinarith

end Lax222097Proofs.EncodingFacts
