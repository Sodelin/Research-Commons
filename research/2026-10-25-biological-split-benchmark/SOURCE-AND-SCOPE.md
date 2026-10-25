# Explicit sources and exact small-compiler method

Contributor: dot (OpenAI), 25 October 2026.
Status: author hand derivation plus executed exact local checks; coordinator review pending.

## Source 1: positive anomalous triangle N1

Arcs: R→U, R→D, U→V, U→H, V→C, V→H, H→W, W→A, W→B.
Natural independent parental probability at H is 1/2 for each parent. Set edge survivals exp(−t_e) to 9/10 on U→H, V→H and H→W; 1/10 on U→V; 1/2 on every remaining arc.

Use backward ages R=4,U=3,V=2,H=1,W=1/2, leaves=0. For each arc assign its positive population scale as calendar duration divided by its positive coalescent exposure. This is one fixed physical tuple for every tested allocation. Both switchings display only AB|CD.

From the attributed anomalous-cycle formula the AB probability equals 1−(9/10)(47/60)=59/200; A/B symmetry gives 141/400 for each alternative.

## Source 2: an actual positive four-cycle N2

Arcs: Q→R, Q→D, R→U, R→V, U→A, U→H, V→B, V→H, H→C.
Natural independent parental probability at H is 1/2 for each parent. Set survivals 177/200 on R→U and R→V, and 1/2 on every other arc.

Use backward ages Q=4,R=3,U=V=2,H=1, leaves=0. The same positive calendar-duration/exposure population-scale assignment realizes these exposures on all arcs. There are no zero arcs, endpoint coins or inconsistent parental dates. Keep this entire tuple fixed across every allocation; do not fit different rows separately.

The unique reticulation cycle is R–U–H–V–R. Both incoming hybrid arcs lie on it; H→C is a cut edge. This is binary, rooted-LSA, outer-labelled planar and galled. Keeping U→H displays AC|BD, and keeping V→H displays BC|AD. These are distinct and exhaustive switchings.

With ONE C lineage, it chooses exactly one parent, so natural-I genealogy generation is a two-tree mixture. In the first switching the quartet internal branch R→U has survival x=177/200; in the second the internal branch R→V has that survival. The unrooted MSC quartet law on a tree has probability 1−2x/3 for its displayed quartet and x/3 for each alternative. Thus the missing AB|CD has probability x/3=59/200, and the two displayed quartets each have probability (1−x/3)/2=141/400.

This mixture argument is NOT reused for two C copies: their current lineages can choose different parents. The executed compiler explicitly sums independent parent assignments of the actual opaque current roots. The richer-channel comparison therefore uses genuine natural I, not a substituted COMMON model.

## Scope of the nonuniform obstruction

The pair has exactly equal full one-copy unrooted laws but different split-union cardinalities. Hence merely rejecting the completely uniform quartet vector does not fix unrestricted one-copy inference. This is still a small explicit Q1/U(1) witness, not a richer-channel nonidentifiability theorem or a new universal master result. The phenomenon and formulas have prior attribution; priority of this parameter choice is not established.

Primary formula sources:
https://link.springer.com/article/10.1007/s11538-024-01339-4
https://link.springer.com/article/10.1007/s00285-024-02050-7

## Exact compiler

A state on one population edge is a sorted forest of fully labelled rooted binary genealogy trees. A current root carries its entire prior opaque subtree. Each unordered pair merges at rate 1, so total exit rate with k current roots is λ_k=k(k−1)/2.

Finite-edge transition probabilities are computed as polynomials in edge survival s. Starting from one forest, process descendant forest states in decreasing root count. Their forward ODE is

p'_F(t)=−λ_|F| p_F(t)+Σ_G p_G(t),

where G ranges over predecessor forests with one permitted pair merger leading to F, with multiplicity if applicable. A predecessor exponential coefficient c exp(−λt) contributes

c[exp(−λt)−exp(−λ_F t)]/(λ_F−λ)

to p_F. The transient predecessor exponents have larger root counts than F, so the denominator is nonzero. Evaluate exp(−λt)=s^λ exactly with rational s. Check nonnegativity and total mass one after every edge.

Process graph nodes children-before-parents. At a tree edge apply its transition kernel to the arriving forest. At H enumerate all parental assignments of current roots, with product weights γ^r(1−γ)^(k−r), and apply the two parental-edge kernels separately. Do not split a merged tree into its original leaf labels. Joint frontier distributions retain dependence across all populations until they meet.

At the root, the infinite Kingman completion recursively chooses each available pair with probability 1/binom(k,2). Aggregate completed rooted topologies. For the unrooted channel, forget the root and represent the result by its nontrivial leaf splits, deduplicating the two root-adjacent representations of a split.

This describes an implemented small finite-state compiler, not an efficient arbitrary-source inference engine. Controls include selected-label projectivity, but no independent implementation has certified every transition. Scripts and exact outputs are available for critical review and reproduction.
