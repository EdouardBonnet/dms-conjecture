# Proof structure

The reduction maps a Max Cut instance (F, k) to (G_F, k + b(F)), where
b(F) is twice the sum of the spans of the edges in the vertex ordering.
Two properties give its correctness: G_F excludes the 5-by-5 grid as an
induced minor, and its independence number is MaxCut(F) + b(F).

## Excluding the induced grid minor

In a row and column graph, a connected vertex set containing at most one
side of each column lies within a single row. Every cycle, including one
represented by branch sets of an induced-minor model, therefore contains
vertices on opposite sides of a column.

The closed neighborhood of these vertices contains the whole column.
For three pairwise nonadjacent cycles, the corresponding columns are
distinct. The middle column separates the other two cycles, which rules
out a path between them avoiding the middle cycle's closed neighborhood.
The three corner squares of the 5-by-5 grid form an asteroidal triple, so
this grid cannot be an induced minor. The property passes to the induced
subgraph G_F.

These arguments are in `ColumnSets`, `CyclePairs`, `InducedModels`,
`Obstruction`, `GridWitness`, and `GridExclusion`.

## Independent sets and cuts

An independent set in G_F chooses at most one side of each column. Its
choices in the columns representing vertices of F determine a cut.
For an edge uv with u < v, its two rows contribute at most 2(v − u)
vertices, plus one if the edge crosses the cut.

Conversely, a cut gives an independent set attaining these contributions.
The upper and lower bounds yield the independence-number identity.
The counting arguments are in `Counting`, `IndependentUpper`,
`IndependentLower`, and `IndependenceIdentity`.

## Polynomial-time constructions

`EncodedReduction` enumerates the retained vertices of G_F.
`GraphFormulas`, `GraphEnumeration`, and `GraphOffset` describe the output
order, adjacency matrix, and threshold shift. `GraphQuery`, `GraphQueryRun`,
and `ReductionTime` implement this enumeration and bound its running time.
`PolynomialComposition` composes the reduction machines, bounding the
intermediate word length by the first machine's running time.

## Max Cut hardness

`ThreeSAT` replaces each three-literal clause by two not-all-equal clauses,
using an anchor variable and an auxiliary variable. `NAEMaxCut` joins
complementary literals and introduces a triangle for each clause.
`SubdividedCut` replaces every edge occurrence by a three-edge path with
fresh internal vertices. The resulting graph is simple and unweighted,
even when literal occurrences repeat.

`ShortCNF` pads unit and binary clauses by repetition. `CNFLookup` scans the
encoded formula; `CNFMachine` implements bounded output loops; and
`CutEnumeration` and `CutMachine` write the graph and threshold.
`CookBridge` identifies the formula encoding with that of the Cook–Levin
compiler and checks that its Tseitin clauses have between one and three
literals. `MaxCutHardness` combines these reductions.

`IndependentSetHardness` composes Max Cut hardness with the construction
of G_F and shifts the threshold by b(F).
