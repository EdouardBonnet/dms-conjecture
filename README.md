# Maximum Independent Set with an excluded planar induced minor

Local Lax submission **lax-762056**, preparing **Theorem 5** of Édouard Bonnet
and Yeonsu Chang's supplied manuscript, *Max Independent Set Remains NP-hard
when Excluding a Planar Induced Minor*.

**Status: the paper's graph proofs and the polynomial-time encoded
construction have complete Lean proofs. Theorem 5 is assembled, with
`MaxCutHard.np_hard` as its one remaining local assumption.** Six of the
eight concept statements are closed. The remaining work is the
Cook–Levin-to-Max-Cut prerequisite: its gadget correctness is proved;
its machine-time implementation and Cook–Levin integration remain open.

The closed proof of [Claim 9](proofs/Lax762056Proofs/GridExclusion.lean) uses
the explicit three-cycle grid witness and the general obstruction for column
graphs. The closed proof of [Claim 10](proofs/Lax762056Proofs/IndependenceIdentity.lean)
combines an upper bound for every independent set with an explicit independent
set constructed from a maximum cut. Neither proof assumes a concept statement.

The main statement is in
[Theorem5.lean](concepts/Lax762056/Theorem5.lean). It says that for every
language in the existing NP, a polynomial-time reduction outputs a graph
excluding the 5-by-5 grid and a threshold, with the input accepted exactly
when the graph has an independent set meeting that threshold. Every output
satisfies the graph-class promise, including outputs on no-instances. There
is no hypothesis assuming Max Cut hardness or the correctness of the reduction.

| Concept | Mathematical content |
| --- | --- |
| [InducedMinors](concepts/Lax762056/InducedMinors.lean) | Disjoint, nonempty connected branch sets with exact adjacency. |
| [Grid](concepts/Lax762056/Grid.lean) | The Cartesian product of two five-vertex paths and its exclusion as an induced minor. |
| [GraphEncoding](concepts/Lax762056/GraphEncoding.lean) | Graph/threshold instances with a fixed binary adjacency-matrix encoding. |
| [MaxCut](concepts/Lax762056/MaxCut.lean) | Unweighted cuts, maximum cut size, and edges counted once. |
| [MaxCutHard](concepts/Lax762056/MaxCutHard.lean) | The classical NP-hardness prerequisite, to be proved using Cook–Levin. |
| [ColumnGraph](concepts/Lax762056/ColumnGraph.lean) | The intermediate graph in Figure 1. |
| [AsteroidalCycles](concepts/Lax762056/AsteroidalCycles.lean) | Three nonadjacent cycles with paths avoiding the third's closed neighborhood. |
| [CycleObstruction](concepts/Lax762056/CycleObstruction.lean) | Such graphs are excluded induced minors; the 5-by-5 grid is one. |
| [Reduction](concepts/Lax762056/Reduction.lean) | The retained vertices of Figure 2 and the additive offset. |
| [GridExclusion](concepts/Lax762056/GridExclusion.lean) | Claim 9 for the intermediate and constructed graphs. |
| [IndependenceIdentity](concepts/Lax762056/IndependenceIdentity.lean) | Claim 10: the exact independence-number/maximum-cut identity. |
| [ReductionTime](concepts/Lax762056/ReductionTime.lean) | An actual polynomial-time machine producing the encoded reduction. |
| [Theorem5](concepts/Lax762056/Theorem5.lean) | The main NP-hardness statement. |

Vertices are indexed from zero. Thus column `2*j` represents the paper's
vertex `v_(j+1)`; an edge's two rows keep opposite sides at their endpoints.
The definition includes empty and edgeless input graphs. The algorithm uses a fixed lexicographic
enumeration of the retained vertices and proves that its output graph is
isomorphic to the graph used in the structural proofs.

The theorem gives the paper's conditional refutations of Conjectures 1 and 4
(unless P = NP) and Conjecture 2 (unless NP is contained in QP). These
interpretations are recorded in the abstract; separate definitions of QP,
CMSO2, weighted optimization, and the conjectures are not included. Neither
Corollary 6's ETH bound nor Conjectures 7 and 8 is a claim of this submission.

The concept package depends on **lax-434930** (classical complexity), which
depends on **lax-554803** (polynomial-time Turing machines). P and NP are reused
without modification. The proof package also pins **lax-979537**'s verified
finite stack-program and formula-evaluation compiler. The reduction has a
single finite machine, with a proved polynomial bound on its actual running
time, including parsing, output, and cleanup. A separate proved composition
machine avoids mathlib's unfinished polynomial-time composition theorem.

These proofs use the exact Turing-machine model of the existing P and NP;
no RAM simulation is needed and **lax-13 is not used**. If a RAM bridge becomes
necessary, it must use **lax-67**.

Cook–Levin currently exists locally as **lax-429075** but has no archive
record. It is therefore not yet a legal pinned dependency. Its anticipated
circuit compiler outputs Tseitin clauses of length one to three. The local
proofs already establish 3-SAT to NAE-3-SAT to simple unweighted Max Cut,
including loops and repeated occurrences in the intermediate construction.
Completing the encoded satisfiability-to-Max-Cut machine and connecting the
archived Cook–Levin interface will close `MaxCutHard.np_hard`; the paper's
construction and the final theorem assembly will not need to change.

Run `lax build . --replay` to validate the definitions, inspect the proof
assumptions, and replay the proofs in the kernel. The complexity and stack-compiler
dependencies are archive drafts. A separate finite sanity check also confirmed
the reduction's identity and vertex count for every graph on at most four
labeled vertices (76 graphs). The general Claims 9 and 10 are proved in Lean,
independently of that finite check.

The scaffold uses the default
archive environment, Lean 4.30.0 and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Generated build files are ignored.
See [PROOF_PLAN.md](PROOF_PLAN.md) for the remaining work and dependency order.
