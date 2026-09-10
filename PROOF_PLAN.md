# Proof plan for Theorem 5

The concept statements are proof obligations, expressed as Lax concept axioms.
They do not assert that a Lean proof has already been written. No `sorry` or
placeholder proof is used. At this preparation stage, the proof package is empty.

1. **Graph encodings and machine infrastructure.** Prove injectivity of the
   adjacency-matrix encoding and provide a parser that rejects malformed words.
   Enumerate vertices by a fixed order, never by an arbitrary equivalence with
   `Fin`. Establish the polynomial-time machine routines needed below and
   composition of the finite Turing machines. In the pinned mathlib,
   `TM2ComputableInPolyTime.comp` is a `proof_wanted`; invoking it would introduce
   `sorryAx` and is not an admissible proof. Prove the needed composition lemma
   locally or cite a completed archive proof. If using a word-RAM implementation,
   use lax-67 and prove the required simulation; the published lax-51 interface
   uses lax-13 and is not the required bridge.

2. **Max Cut hardness.** When Cook–Levin is archived, pin lax-429075's concept
   package in `proofs/lakefile.toml`. Import its `CookLevin` and encoding
   interfaces. Reduce its binary CNF satisfiability language to simple unweighted
   Max Cut, checking each gadget, its threshold, and polynomial computation.
   One route is CNF to 3-SAT to not-all-equal 3-SAT to Max Cut. If an intermediate
   construction uses edge weights or parallel edges, remove them with explicit
   gadgets and polynomial size bounds. Handle malformed CNF words with a fixed
   no-instance. This discharges `MaxCutHard.np_hard`; Cook–Levin alone does not.
   The classical reference for simple unweighted Max Cut is
   [Garey–Johnson–Stockmeyer (1976)](https://doi.org/10.1016/0304-3975%2876%2990059-1).

3. **Induced-minor infrastructure.** Prove transitivity, invariance under graph
   isomorphism, and that induced subgraphs are induced minors. Check that
   connectivity in `Model` includes nonemptiness. Prove the cycle-lifting
   lemma: the union of connected branch sets over a cycle contains a cycle.
   Preserve all nonadjacencies when lifting avoiding paths and cycles.

4. **Cycle obstruction.** In a cycle of a column graph, choose a vertex in a
   leftmost column. Either the cycle already contains an edge within a column,
   or its two cycle neighbors occupy opposite sides in the next column. Thus
   each lifted cycle meets both sides of some column. Three pairwise
   nonadjacent lifted cycles give three distinct such columns. The middle
   column lies in the middle cycle's neighborhood and separates the two outer
   cycles, contradicting the avoiding path. This proves
   `CycleObstruction.excludes_triple`.

5. **The fixed grid witness and Claim 9.** For `grid_has_triple`, use the unit
   squares with lower-left coordinates `(0,0)`, `(0,3)`, and `(3,0)` in the
   zero-based 5-by-5 grid. The top and left boundary paths join the first
   square to the other two. The right and bottom boundary path joins the
   other two while avoiding the first square's closed neighborhood. Check
   the finite walks, cycles, disjointness, and avoidance directly. Apply the
   cycle obstruction, then induced-subgraph monotonicity, to discharge both
   `GridExclusion` statements.

6. **Claim 10.** Prove both bounds for `IndependenceIdentity.identity`. A cut
   yields a compatible independent set by the choices in Figure 5. Conversely,
   an independent set meets only one side per column. Assign an empty vertex
   column an arbitrary fixed side. In the two rows of an edge of span `d`,
   at most `2*d+1` vertices can be chosen, and attaining that bound forces
   the endpoint columns to choose opposite sides. Prove this last implication
   explicitly; the paper's final upper-bound observation is a substantive
   combinatorial step. Sum over edges, each represented once.

7. **Reduction computation.** Enumerate increasing endpoint pairs, the two
   row labels, columns, and sides in order, retaining exactly `Reduction.kept`.
   Output the adjacency matrix of the resulting enumeration and the threshold
   `k + offset F`. An edge of span `d` contributes `8*d` retained vertices,
   so `|V(G_F)| = 8*sum(d) <= 8*n*|E(F)|`; the full matrix still has polynomial
   size. Prove the isomorphism and a polynomial bound on the actual machine's
   execution, including input scanning, output writing, and computing the
   unary threshold. This discharges `ReductionTime.polynomial_time`.

8. **Assembly.** Compose the Max Cut reduction with the encoded construction,
   using proved composition infrastructure. Transfer `GridExclusion.reduction`
   and `IndependenceIdentity.identity` across the output isomorphism. Finally
   cancel the additive offset in
   `k + offset F <= maxCut F + offset F`. The resulting reduction proves
   `Theorem5.np_hard`, with graph-class membership on every input.

Lax proof annotations should name each discharged statement and let the
inspector compute the assumptions. The final graph should have no open local
prerequisites, and its only external theorem dependencies should be explicit
archive statements (including Cook–Levin when available).
