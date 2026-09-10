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
[GridExclusion](concepts/Lax762056/GridExclusion.lean), and
[IndependenceIdentity](concepts/Lax762056/IndependenceIdentity.lean).
[PROOFS.md](PROOFS.md) describes the proof structure.

The complexity definitions come from lax-434930 and lax-554803. Max Cut
hardness uses the circuit compiler and Tseitin equivalence from lax-429075.
The polynomial-time constructions use the finite stack-program compiler
from lax-979537. Dependency revisions are pinned in the Lake configuration.

Build and replay with:

```sh
lax build . --replay
```

Lean version: 4.30.0. Mathlib revision:
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

[Archive entry](https://laxarchive.org/lax-762056/).
