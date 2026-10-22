# Exact complexity of Carta-score polytomy refinement

Author: dot (OpenAI). Date: 22 October 2026.
Status: complete hand proof with independently scoped hand-review PASS recorded below; no runtime or Lean verification; historical novelty not certified.

## 1. Problem and result

Let S be a finite set of terminal cell types. A differentiation map F has explicitly given distinct nonempty potency-set vertices, root S, singleton sinks, strict subset edges, and exact singleton reachability consistent with each potency. A cell lineage tree T has distinctly identified cells at its leaves, with possibly repeated type labels tau. For each vertex v let B_T(v) be its descendant terminal-type set.

A compatible potency labeling ell assigns a vertex of F to every lineage vertex, assigns {tau(w)} to each leaf, and has ell(parent) reaching ell(child). This implies B_T(v) subset ell(v). Define

D_lambda(T,F,ell) = sum_v c(ell(v) minus B_T(v)) + sum_(u,v) r_lambda(ell(u),ell(v)),

where c(A)=sum_(t in A) w_s(t), with nonnegative rational weights, and r_lambda(P,Q) is the given nonnegative resolution cost on reachable pairs. In the Carta sampling/resolution objective it is lambda*w_r(P,Q) when P differs from Q and there is no direct edge P->Q, and zero for self transitions or direct edges. Unreachable pairs are forbidden.

Given a rooted input lineage tree T0 with no unary vertices, a binary refinement replaces every multifurcation by a rooted binary tree on its child subtrees, preserving all original leaf identities and clades. The objective is

OPT(T0,F) = min_(T binary refinement of T0) min_(ell compatible) D_lambda(T,F,ell).

**Theorem A (hardness already for a differentiation star).** The decision problem OPT(T0,F) <= gamma is NP-complete even when:
- F is the star differentiation tree with vertices S and all singletons;
- sampling weights are all one;
- T0 has exactly one multifurcation, at its root, and all its child subtrees are already binary;
- every lineage internal vertex has at least two distinct observed types below it;
- every compatible labeling is forced: all internal vertices receive S;
- the resolution cost is identically zero, so the conclusion applies to every fixed nonnegative lambda in the usual Carta objective.

The terminal alphabet and root degree are unbounded input parameters. Composite child clades and repeated cell types across different child clades are essential permitted features of this construction. This theorem does not assert hardness for a polytomy whose children are all single leaves, a fixed-size terminal alphabet, or bounded degree.

**Theorem B (exact degree-parameterized algorithm).** For an arbitrary explicitly supplied differentiation DAG, arbitrary composite child subtrees, fixed observed leaf types, and the full nonnegative rational D_lambda, the optimum is computed exactly by the subset dynamic program in Section 7. If M=|V(F)| and d_v is the degree of each original internal lineage vertex, the arithmetic-operation cost is

O(sum_v [3^(d_v) M + 2^(d_v) M^2 + 2^(d_v) M |S|]),

after reachability preprocessing. In particular the problem is fixed-parameter tractable in maximum polytomy degree, with polynomial dependence on the explicit differentiation map and lineage-tree input. Rational arithmetic bit complexity is polynomial per operation in the original bit lengths and tree size.

No inference claim about biological transition identifiability follows from either theorem.

## 2. Classical source problem

Min-sum set cover (MSSC): given a nonempty universe U of N elements and sets C1,...,Cm whose union is U, order all m sets. For each x in U let j_x be the first index in that order of a set containing x. Minimize sum_x j_x.

This problem is NP-hard. A primary source is Uriel Feige, Laszlo Lovasz, and Prasad Tetali, *Approximating Min Sum Set Cover*, Algorithmica 40, 219–234 (2004), DOI https://doi.org/10.1007/s00453-004-1110-5 ; author-hosted manuscript https://tetali.math.gatech.edu/PUBLIS/mssc_final.pdf . Its hardness-of-approximation theorem implies exact optimization hardness. The integer-threshold decision version is in NP because an ordering is a polynomial certificate, hence is NP-complete. We use that classical result, not a newly claimed proof of MSSC hardness.

One may restrict to m>=2 and thresholds K with N <= K <= mN: instances outside these bounds are trivial and may be handled separately. Let OPT_MSSC denote the optimum.

## 3. A caterpillar lemma for decreasing merge costs

Let I be a finite set of blocks and let f be a nonnegative real-valued function on its nonempty subsets satisfying f(J) >= f(K) whenever J subset K. For a rooted full binary tree R on the blocks, give each internal vertex w cost f(I_w), where I_w is its descendant-block set. Let C(R) be their sum.

**Lemma.** Some minimizing binary tree is a rooted caterpillar, meaning its internal descendant sets are prefixes of an ordering of the blocks of sizes 2,3,...,|I|. More strongly, every binary tree admits a caterpillar of no larger cost.

**Proof by induction on |I|.** The assertion is immediate for one or two blocks. At the root let the child block sets be A and B, oriented so f(A)<=f(B). Suppose B has q leaves/blocks. Remove the internal topology on B and attach its q individual blocks, in any order, one at a time above the unchanged subtree on A. The final root set remains A union B, so its cost is unchanged. There are q-1 other new attachment nodes, each containing A and hence each having cost at most f(A). Previously the subtree on B had q-1 internal nodes; each had descendant set J subset B and therefore cost at least f(B)>=f(A). Thus these replacement costs do not increase the sum. The internal costs of the subtree on A are unchanged. By induction replace that subtree by a no-more-expensive caterpillar, preserving its total descendant set A and therefore all attachment costs. The final tree is a caterpillar on I. This also covers q=1, where both counted collections are empty. QED.

This is an existence/structural reduction, not a polynomial algorithm for finding the best ordering.

## 4. Polynomial construction from MSSC

Start from (U,C1,...,Cm), with N=|U|. Set H=mN+1. Introduce H new private types Z={z1,...,zH} and two common marker types a,b, all disjoint from U. Define

S = U disjoint-union Z disjoint-union {a,b}.

Let F be the differentiation star S->{t} for all t in S. All sampling weights are one.

Construct m+1 child subtrees, called blocks. The anchor block has descendant-type set

B0 = Z union {a,b}.

Set block i, for i=1,...,m, has descendant-type set

Bi = Ci union {a,b}.

For each block make any fixed rooted binary tree whose leaves contain exactly one cell of every type in Bi. All cell identities are distinct, even when their terminal types agree across blocks. Every block has at least two leaves, because a,b are present. Inside a block all leaf types are distinct. Let T0 have one root with these m+1 block roots as children; all block-internal trees are retained unchanged. This is a polynomial-size construction: H is O(mN), the anchor has H+2 leaves, and the other blocks have at most N+2 leaves each.

Every internal vertex of every refinement lies either within a fixed block or joins whole blocks. A fixed-block internal vertex has at least two different descendant types. A joining vertex contains both a,b. Therefore no internal vertex can be labeled by a singleton state of F. Its unique feasible label is S. Conversely assigning S to all internal vertices and the observed singleton to each leaf is compatible.

All lineage edges then either join S to S or S to a singleton. Self transitions and all these star edges have zero resolution cost. Hence D_lambda=D_0 for the unique labeling, regardless of lambda.

Let C0 be the sum of |S minus B(v)| over all internal vertices lying within the fixed blocks, including their roots. This is a polynomially computable integer independent of the refinement. The remaining cost is over the internal joining tree on the m+1 blocks, with

f(I) = |S minus union_(i in I) Bi|.

This f is nonnegative and inclusion-decreasing. The root joining set includes all types, so its cost is zero, though it may harmlessly remain in the sum.

## 5. Exact optimum identity

By the caterpillar lemma, an optimum joining tree can be chosen as a caterpillar. Let its ordering have anchor at position p. For each type t, let r_t be the first position of a block containing t. The joining internal sets are prefixes of sizes k=2,...,m+1. Type t is missing from precisely the prefixes with k<r_t. Its contribution is therefore max(r_t-2,0).

Each common marker has r_t=1 and contributes zero. Each private type z has r_z=p. Thus the private types contribute H*max(p-2,0).

There exists a caterpillar with anchor first and any ordering of the real set blocks thereafter, whose private-type contribution is zero and whose U contribution is at most (m-1)N. Since H=mN+1>(m-1)N, no optimum caterpillar can have p>=3. It follows that some optimal caterpillar has anchor among its first two blocks. Interchanging the first two blocks leaves every internal prefix unchanged, so assume without loss of generality the anchor is first.

Now let j_x be the first position of a real set containing x in the subsequent ordering of C1,...,Cm. Since the anchor contains no U element, r_x=j_x+1. Thus x contributes j_x-1 and the total joining cost is

sum_(x in U) (j_x-1) = sum_(x in U) j_x - N.

Conversely, every ordering of the MSSC instance yields precisely this cost by placing the anchor first. Therefore the exact identity is

**OPT(T0,F) = C0 + OPT_MSSC - N.**

This equality controls all binary refinements through the caterpillar lemma; it does not optimize only a selected subclass without justification.

For a threshold K in the nontrivial MSSC range, set gamma=C0+K-N, a nonnegative integer of polynomial encoding length. The identity proves both directions:

MSSC has an ordering of cost <=K if and only if T0 has a binary refinement with Carta discrepancy <=gamma.

This is a polynomial many-one reduction to the original total-discrepancy problem, not to a substitute clade-packing problem. It proves the NP-hardness part of Theorem A, already on star differentiation trees with one progenitor potency.

## 6. NP membership

A certificate consists of a binary refinement T and a compatible label assignment ell. A binary refinement has polynomially many vertices in the input tree size: replacing a degree-d multifurcation uses d-1 binary internal vertices in place of one. One can check leaf identities and labels, verify that contracting the new refinement edges recovers T0, compute all descendant-type sets, check the supplied differentiation graph's reachability, validate every assigned transition, and sum the rational objective in polynomial time. The integer threshold and unit-weight star restriction are a special case. Thus the decision problem in Theorem A is NP-complete.

For arbitrary rational inputs this certificate proves NP membership as well, provided the graph and weights are given explicitly with finite binary encodings. No claims about arbitrary real-number encodings are needed.

## 7. Exact subset dynamic program for the full objective

Process original lineage vertices bottom-up. For an original vertex v, let its children be v1,...,vd, with already known descendant sets Bi and already computed arrays L_i(Q): the minimum full score over all binary refinements of the child subtree, conditional on that child's root state Q. At a leaf w the array is zero at {tau(w)} and infinity elsewhere.

For every nonempty index subset I subset {1,...,d}, let B(I)=union_(i in I) Bi. Define H_v(I,P) as the minimum score of a binary joining subtree on exactly those child subtrees, conditional on its root state P. This score includes all child-subtree scores and all joining vertices/edges in that subtree. A singleton subset introduces no new vertex:

H_v({i},P) = L_i(P).

For each available H_v(I,.) define its parent-message transform

A_v(I,P) = min_(Q reachable from P) [r_lambda(P,Q) + H_v(I,Q)].

For |I|>=2, the exact recurrence is

H_v(I,P) = infinity, if B(I) is not a subset of P;

H_v(I,P) = c(P minus B(I)) + min_(empty != J proper-subset I) [A_v(J,P)+A_v(I minus J,P)], otherwise.

To avoid counting the same unordered split twice, require the smallest index of I to belong to J; for minimization this is optional. Evaluate in increasing |I|, so the two child arrays in each term are already known. Set L_v(P)=H_v({1,...,d},P). The final optimum is min_P L_root(P), or L_root(S) if an additional root-S convention is imposed explicitly.

**Proof.** The claim defining each array is proved simultaneously by induction on original-subtree size and subset size. A singleton joining object is exactly the corresponding already optimized original child subtree. Every binary joining object with at least two children has a root P and a unique split of the child-index set into two nonempty parts J and I minus J. Its cost decomposes into the root's sampling cost, the two edge costs, and the two child joining costs. Compatibility requires the child roots to be reachable from P and B(I) subset P. Conversely any admissible choices in the recurrence glue to a compatible binary joining tree. Minimizing the exact decomposition establishes equality, not merely an upper bound. The same logic applies independently at every original multifurcation, while the arrays retain all interactions through their root states. QED.

For a degree-d node, the transforms cost O(2^d M^2), the split minimizations cost O(3^d M), and explicit set-union/node-weight preprocessing costs O(2^d M |S|). These bounds also cover d=2. The recurrence does not require laminar potencies or independent child observations; it is deterministic optimization on the supplied tree and weights.

## 8. Consequences and limitations

The hardness theorem rules out a general polynomial-time laminar-versus-DAG dichotomy under the stated arbitrary-composite-child input model, unless P=NP. The differentiation map in the reduction is the simplest laminar tree and the assignment optimization has no freedom. The difficulty comes from ordering/grouping observed descendant sets across the unresolved lineage node, not from overlapping differentiation potencies.

The result does not say that laminar structure is useless, or that simpler restricted input classes are hard. In particular, bounded-degree inputs have the exact algorithm above, and the all-single-leaf-child domain deserves separate analysis. Likewise the elementary example with AB,AB,CD,CD children only refutes a particular label-count argument; the full MSSC reduction is the complexity proof.

This contribution is a theorem about a deterministic objective. It supplies neither a stochastic generative law nor a biological target-identification theorem, and it does not resolve the separate unknown-state cellular observation problem. No source code was executed; no Lean/Lake compilation was performed. A future formalization must include the refinement definition, decreasing-cost caterpillar lemma, exact construction and cost identity, and a precise complexity reduction interface. Historical novelty needs separate literature comparison.

## 9. Prior-work comparison at this checkpoint

Carta's published NP-hardness results concern inferring a differentiation map or differentiation tree from supplied lineage trees. The result above holds the differentiation map fixed, in fact a star, and optimizes a refinement of the lineage tree. Those are different optimization variables. Carta's fixed-tree progenitor-labeling dynamic program is also distinct: in the hardness construction the labeling is unique and the unresolved lineage topology carries the difficulty. Source: https://pmc.ncbi.nlm.nih.gov/articles/PMC12982130/ , Methods, definitions of PLP, CDMIP and CDTIP.

The reduction deliberately credits classical MSSC hardness. Searches combining polytomy refinement, cell differentiation, and min-sum set cover did not locate a prior exact instance of this reduction in the sources retrieved at this checkpoint. That limited search is not a historical novelty certificate. The caterpillar lemma may also be useful in other decreasing merge-cost problems; no originality claim for that general lemma is asserted.

## 10. Independent review

At 07:12 UTC, the coordinating dot parent independently hand-reviewed the complete proof and verified the primary MSSC source. Scoped PASS covered the caterpillar replacement, unit-weight anchor construction, all-refinement optimum identity and threshold, zero resolution cost, NP membership, and general-DAG subset recurrence/complexity. The separate review record is `POLYTOMY-REVIEW-20261022-0712Z.md`. This is not a runtime, Lean, empirical, or historical novelty certificate.
