# Proof status and remaining work

Five of the eight concept statements have complete Lean proofs with no
archive-statement assumptions. The full Theorem 5 is not yet proved.

| Statement | Status | Proof |
| --- | --- | --- |
| `CycleObstruction.grid_has_triple` | Closed | `GridWitness.grid_has_triple` |
| `CycleObstruction.excludes_triple` | Closed | `Obstruction.excludes_triple` |
| `GridExclusion.intermediate` | Closed | `intermediate_excludes_grid` |
| `GridExclusion.reduction` | Closed | `reduction_excludes_grid` |
| `IndependenceIdentity.identity` | Closed | `independence_identity` |
| `MaxCutHard.np_hard` | Open | Cook–Levin and satisfiability-to-Max-Cut reductions |
| `ReductionTime.polynomial_time` | Open | Encoded reduction and machine-time analysis |
| `Theorem5.np_hard` | Open | Composition and assembly |

Proof names have prefix `Lax762056Proofs.`; statement names have prefix
`Lax762056.`. The proof package contains no new axioms or placeholder proofs.

## Completed graph proofs

`GridWitness` specifies the three corner squares at `(0,0)`, `(0,3)`, and
`(3,0)`, with boundary paths avoiding the third square's closed neighborhood.
Their finite properties are checked by kernel reduction, without `native_decide`.

`ColumnSets` proves that a connected set choosing at most one side of each
column stays in a single row and occupies an interval of columns. Two
disjoint such sets that are adjacent touch at their interval endpoints.
`CyclePairs` applies this to the branch sets of a cycle: a branch set with
minimum right endpoint would have two neighbors meeting the same next-column
vertex, contradicting disjointness. Every represented cycle therefore
contains opposite sides of some column.

`InducedModels` proves that connected target sets lift to connected unions
of branch sets and that induced-minor models lift from induced subgraphs.
`Obstruction` orders the three columns from `CyclePairs`; the middle column
separates the outer cycles. Lifting an avoiding path contradicts the
separation. `GridExclusion` specializes to the fixed grid, proving Claim 9
for both the intermediate and retained graphs.

For Claim 10, `Counting` pairs consecutive positions to bound a row's
contribution. Attaining `d+1` in a row of length `2*d+1` forces both endpoints.
`IndependentUpper` constructs a cut from any independent set and proves an
edge contributes at most `2*d+1`, or at most `2*d` when it does not cross the
cut. `IndependentLower` explicitly chooses vertices from a cut, omitting the
penultimate column for an uncut edge. It proves independence, injectivity of
the enumeration, and the exact cardinality. `IndependenceIdentity` combines
the bounds. Empty and edgeless graphs are included.

## Remaining complexity proofs

1. **Encodings and machine infrastructure.** Prove injectivity of the graph
   encoding and implement parsing and construction routines with a fixed
   computable vertex enumeration. Prove the needed machine composition lemma:
   in the pinned mathlib, `TM2ComputableInPolyTime.comp` is a `proof_wanted`,
   so invoking it introduces `sorryAx`. A RAM implementation must use lax-67
   with a proved simulation; the published lax-51 interface imports lax-13.

2. **Max Cut hardness.** Once Cook–Levin is archived, pin lax-429075's concept
   package in `proofs/lakefile.toml`. Reduce its binary CNF satisfiability
   language to simple unweighted Max Cut, proving the gadget equivalences
   and polynomial computation. One route is CNF to 3-SAT to not-all-equal
   3-SAT to Max Cut. Remove any intermediate weights or parallel edges with
   explicit polynomial-size gadgets. Map malformed words to a fixed
   no-instance. The classical reference is
   [Garey–Johnson–Stockmeyer (1976)](https://doi.org/10.1016/0304-3975%2876%2990059-1).

3. **Reduction time.** Enumerate increasing endpoint pairs, row labels,
   columns, and sides, retaining exactly `Reduction.kept`. Output the
   adjacency matrix and threshold `k + offset F`. An edge of span `d`
   contributes `8*d` vertices, so the matrix has polynomial size. Prove a
   polynomial bound on the machine's execution, including scanning, output,
   and computing the unary threshold. A graph-size bound alone does not
   discharge `ReductionTime.polynomial_time`.

4. **Assembly.** Compose the reductions, transfer the closed graph proofs
   across the output isomorphism, and cancel the common threshold offset.
   Preserve the graph-class promise on every input, including no-instances.

Corollary 6 and its ETH/sparsification prerequisites are outside the scope.
