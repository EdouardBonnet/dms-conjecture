import Lax762056.ReductionTime
import Lax762056Proofs.GraphOffset

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs

open Lax762056 GraphEncoding Reduction

/-- Output the order, matrix, and offset; the runner appends the input threshold. -/
def reductionQuery : GraphQuery.Q :=
  .seq GraphEnumeration.header
    (.seq (.emit .truth (GraphFormulas.constant false))
      (.seq GraphEnumeration.matrix GraphOffset.query))

theorem reductionQuery_encoding (I : Instance) :
    GraphQuery.render reductionQuery I = encode (EncodedReduction.reduce I) := by
  rw [GraphQuery.render]
  simp only [reductionQuery, GraphEnumeration.word_seq, GraphEnumeration.word_emit,
    GraphFormulas.value_truth, GraphFormulas.value_constant, GraphEnumeration.word_header,
    GraphEnumeration.word_matrix, GraphOffset.word_query]
  rw [GraphQuery.encode_eq, GraphEnumeration.encoded_matrix]
  simp [EncodedReduction.reduce, unary, List.replicate_add, -List.replicate_append_replicate, List.append_assoc,
    Nat.add_comm I.threshold]

/--
---
conclusion: Lax762056.ReductionTime.reduction_polynomial_time
---
Enumerate the retained vertices and their adjacency matrix, then add the
offset to the threshold. The enumeration and adjacency tests take polynomial time.
-/
theorem reduction_polynomial_time :
    ∃ f : Instance → Instance,
      PolynomialTime f ∧
      ∀ I, Nonempty ((f I).graph ≃g reductionGraph I.graph) ∧
        (f I).threshold = I.threshold + offset I.graph := by
  obtain ⟨machine⟩ := GraphQuery.polynomial_time reductionQuery
  refine ⟨EncodedReduction.reduce, ⟨{ machine with outputsFun := ?_ }⟩, ?_⟩
  · intro I
    simpa only [id_eq, reductionQuery_encoding] using! machine.outputsFun I
  · intro I
    exact ⟨⟨EncodedReduction.iso I⟩, EncodedReduction.threshold I⟩

end Lax762056Proofs
