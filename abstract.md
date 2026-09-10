We state Theorem 5 of Bonnet and Chang: Maximum Independent Set is NP-hard
on graphs excluding the $5\times5$ grid as an induced minor. The reduction
from Max Cut constructs a graph $G_F$ in this class satisfying
$\alpha(G_F)=\operatorname{MaxCut}(F)+2\sum_{uv\in E(F),\,u<v}(v-u)$.
The formalization specifies induced minors, the construction, the structural
cycle obstruction, the independence-number identity, binary graph encodings,
and the polynomial-time reduction. It reuses the archive's definition of NP.

The result rules out the polynomial-time algorithms conjectured by
Dallard–Milanič–Štorgel and in the corresponding weighted induced-subgraph
generalization unless $\mathrm{P}=\mathrm{NP}$. The quasipolynomial-time
conjecture of Gartland–Lokshtanov and Korhonen would imply
$\mathrm{NP}\subseteq\mathrm{QP}$.

This is a concept draft: the proof obligations are open. The planned proof of
the Max Cut hardness prerequisite will use the Cook–Levin submission currently
in preparation. The ETH lower bound in Corollary 6 is outside this submission.
