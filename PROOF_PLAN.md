# Proof status and structure

All eight concept statements have Lean proofs. Six use only Lean's standard
axioms. Max Cut hardness and Theorem 5 additionally use the proved circuit
compiler and Tseitin correctness from the published lax-429075 submission.
There are no remaining open local statements.

| Statement | Status | Proof |
| --- | --- | --- |
| `CycleObstruction.grid_has_triple` | Closed | `GridWitness.grid_has_triple` |
| `CycleObstruction.excludes_triple` | Closed | `Obstruction.excludes_triple` |
| `GridExclusion.intermediate` | Closed | `intermediate_excludes_grid` |
| `GridExclusion.reduction` | Closed | `reduction_excludes_grid` |
| `IndependenceIdentity.identity` | Closed | `independence_identity` |
| `MaxCutHard.np_hard` | Proved from lax-429075 | `maxCut_np_hard` |
| `ReductionTime.polynomial_time` | Closed | `reduction_polynomial_time` |
| `Theorem5.np_hard` | Proved from lax-429075 | `theorem5` |

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

## Completed complexity infrastructure

`TM2Bounds`, `TM2Composition`, `TM2Transfer`, and `PolynomialComposition`
prove sequential composition in the existing finite-machine model. The
construction transfers the intermediate word through two linear passes and
bounds its length by the first machine's running time. It does not invoke
mathlib's `TM2ComputableInPolyTime.comp`, which is a `proof_wanted` in the
pinned mathlib.

`EncodedReduction` enumerates retained vertices in a filtered lexicographic
list. `EncodingFacts` proves that the graph encoding is injective and bounds
the output size. `QueryProgram`, `QueryLoop`, and `QueryBounds` compile bounded
tuple enumeration and formula tests into a finite stack machine and bound
its execution. They use the pinned, proved stack compiler from lax-979537.

`GraphQuery` and `GraphQueryRun` parse the input graph's unary order and dense
matrix, run a query, append the unary threshold, and clear all work stacks.
`GraphFormulas`, `GraphEnumeration`, and `GraphOffset` identify the query's
output with the retained-vertex count, exact adjacency matrix, and twice the
sum of the input edges' spans. `ReductionTime` proves the polynomial-time
statement for this actual machine. Empty and edgeless input graphs are
included.

`IsoTransport` transfers induced-minor exclusion and independence numbers
across the algorithm's output isomorphism. `Theorem5` composes the reductions,
uses the closed graph and machine proofs, and cancels the common threshold
offset. It invokes the proved `maxCut_np_hard`, so its only archive-statement
assumptions are the two proved Cook–Levin prerequisites.

## Completed Cook–Levin prerequisite

The semantic gadget chain is checked:

- `ThreeSAT` reduces three-literal OR clauses to NAE clauses, using an anchor
  variable and one auxiliary variable per clause. Global complementation
  normalizes the anchor in the reverse implication.
- `NAEMaxCut` uses complementary literal vertices and clause triangles.
- `SubdividedCut` replaces every edge occurrence by a length-three path with
  fresh internal vertices. This produces a simple unweighted graph even
  when occurrences repeat or have identical endpoints.
- `CutScores` supplies exact path and triangle bounds. The resulting graph
  for a formula with n variables and m clauses has 4n + 16m + 4 vertices and
  threshold 3n + 19m + 3.

`ShortCNF` pads one- and two-literal clauses by repetition, uses the input
word length L as both the variable and clause bound, and fills unused clause
positions with tautologies. It proves satisfiability equivalence and an
output graph of order 20L + 4 with threshold 22L + 3.

`CNFScan`, `CNFPrefix`, `CNFLiteral`, `CNFLiteralSpec`, `CNFHead`, and
`CNFLookup` now implement clause traversal and padded literal lookup in a
finite stack program. Lookup with clause index i has time at most
(2L + 5)i + 15L + 35, and returns the literal specified by `toThreeSAT`.
`StackEqual` and `StackCount` supply checked unary comparison and input-length
counting. `CNFAtom` and `CNFAtomLiteral` implement the equality and signed-literal
queries, including restoration of all work stacks. `CNFWriter`,
`CNFWriterLoop`, and `CNFMachine` compile bounded output queries into a
complete finite machine with a polynomial running-time bound, including
input-length counting and final cleanup. The machine passes the standard
axiom audit. `CutVertices` provides a fixed enumeration and bijection with
the gadget vertices; `MaxCutIso` proves invariance under this relabeling.

`CutEndpoints` identifies the gadget's edges through typed endpoint labels.
`CutTests` implements their adjacency predicate using coordinate equality
and signed literal lookups. `CutEnumeration` writes the vertices and the full
adjacency matrix in the order specified by the graph encoding, and proves
that relabeling preserves maximum cut size. `CutMachine` adds the order and
threshold fields and proves equality of the complete output word with the
encoded graph. The construction and running-time proof hold for every
encoded formula; its satisfiability equivalence requires nonempty clauses
of size at most three.

`CookBridge` proves that lax-429075's binary formula encoding equals the
local encoding, and that every Tseitin clause is nonempty and has size at
most three. It reuses the published circuit compiler, composes it with the
proved Max Cut machine, and applies Tseitin correctness. `MaxCutHard`
specializes this result to the verifier and certificate polynomial supplied
by membership in the existing NP.

Validation passed on 2026-09-10: `lax build . --replay` checked all 13 concepts
and 8 annotated proofs, including kernel replay, in 2m54s. A separate axiom
audit confirmed the exact dependency sets described above. The complexity,
Cook–Levin, and stack-compiler dependencies
are archive drafts pinned at their published source commits.

P and NP retain their existing definitions. No proof uses lax-13. Any future
RAM implementation must use lax-67 and a proved bridge to the time model.
Corollary 6 and its ETH/sparsification prerequisites are outside the scope.
