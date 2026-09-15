# Independent Set without a 5×5 induced grid minor

Maximum Independent Set is NP-hard on graphs excluding the 5-by-5 grid as
an induced minor. The reduction of Bonnet and Chang maps a graph F to a graph
G_F in this class with

```text
α(G_F) = MaxCut(F) + 2 ∑_{uv ∈ E(F), u < v} (v − u).
```

The [main theorem](concepts/Lax762056/IndependentSetHardness.lean) states
`NPHardOn IndependentSet (ExcludesInducedGrid 5)`, with `GraphProblems` and
`Grid` open.
The reductions in `NPHardOn` produce graphs in the specified class on every
input. [GraphProblems](concepts/Lax762056/GraphProblems.lean) defines the
decision problems and hardness predicates;
[GraphEncoding](concepts/Lax762056/GraphEncoding.lean) specifies their encoding.
The [grid predicate](concepts/Lax762056/Grid.lean) takes the side length as
a parameter and excludes the corresponding square grid as an induced minor.

The construction and its structural properties are in
[Reduction](concepts/Lax762056/Reduction.lean),
[ColumnGridExclusion](concepts/Lax762056/ColumnGridExclusion.lean),
[GridExclusion](concepts/Lax762056/GridExclusion.lean), and
[IndependenceIdentity](concepts/Lax762056/IndependenceIdentity.lean).
[PROOFS.md](PROOFS.md) describes the proof structure.

The complexity definitions come from [lax-434930](https://laxarchive.org/lax-434930/). Max Cut
hardness uses the circuit compiler and Tseitin equivalence from [lax-429075](https://laxarchive.org/lax-429075/).
Both dependencies are registered on Mathlib 4.33.0. The polynomial-time constructions
include the required formula-evaluation and stack-program routines from
[lax-979537](https://laxarchive.org/lax-979537/) locally under `QueryDefinitions`
and `QueryCompiler`, with compatibility fixes for Lean 4.33.0. These sources
come from Szymon Toruńczyk and Codex 6's Immerman–Vardi proof package at
commit `82ef67e68fab884dc4cff117a1b871567bdaaafd`. Its abstract result axioms
are omitted from the private definitions; the corresponding checked proofs
are included. Dependency revisions are pinned in the Lake configuration.

Build and replay with:

```sh
lax build . --replay
```

Lean version: 4.33.0. Mathlib revision:
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The annotated paper is in [paper/main.tex](paper/main.tex). Its mathematical
text, proofs, authors, and figures are preserved.

[Archive entry](https://laxarchive.org/lax-762056/).
