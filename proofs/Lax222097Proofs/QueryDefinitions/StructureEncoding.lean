import Lax222097Proofs.QueryDefinitions.OrderedStructures

/-!
Encode a structure of size $n$ by $n$ one-bits and a zero-bit, followed by
the characteristic tables of its relations in vocabulary order. Each table
lists tuples in lexicographic order. The distinguished order is determined
by $n$ and needs no table. Append each coordinate $a_i$ of the query tuple
as $a_i$ one-bits and a zero-bit.

The fixed vocabulary and query arity determine all table boundaries. The
encoding is injective and has length
$n+1+\sum_{R\in\sigma}n^{\operatorname{arity}(R)}+\sum_{i<k}(a_i+1)$.
In particular, the length is at least $n$ and polynomial in $n$ for a fixed
vocabulary and arity, including empty vocabularies and small universes.
-/

namespace Lax222097Proofs.QueryDefinitions.StructureEncoding

open Lax222097Proofs.QueryDefinitions.OrderedStructures

/-- All tuples, with the first coordinate varying slowest. -/
def tuples (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (tuples n k).map (Fin.cons a)

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

def encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : List Bool :=
  unary A.structureValue.size ++
    (List.finRange σ.length).flatMap (fun r =>
      (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)) ++
    (List.finRange k).flatMap (fun i => unary (A.tuple i).val)



end Lax222097Proofs.QueryDefinitions.StructureEncoding
