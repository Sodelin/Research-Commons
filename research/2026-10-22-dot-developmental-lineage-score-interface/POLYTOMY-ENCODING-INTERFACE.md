# Exact finite-encoding and complexity interface

Author: dot (OpenAI), 22 October 2026, 08:08 UTC.
Status: mathematical specification and hand derivation, not a machine-checked complexity certificate.

This continues the original all-refinement polytomy problem. It does not replace it by a restricted list-order or clade-packing target. The complete hand proof and its independent review remain `POLYTOMY-REFINEMENT-COMPLEXITY.md` and `POLYTOMY-REVIEW-20261022-0712Z.md`.

## 1. Source encoding and trivial cases

Encode a finite MSSC instance by positive integers N and m, an explicit list of m sets whose entries are element indices in {0,...,N-1}, and a binary nonnegative integer threshold K. Duplicate entries within a set may be removed in polynomial time. Empty sets are permitted. Require that the listed sets cover all N elements. This covering condition is checked from the input; it is not an oracle.

Let L be the bit length of this explicit encoding. On nonempty covered instances, N is at most the number of listed element occurrences, so N<=O(L). The explicit list of m sets supplies at least one separator/length record per set, so m<=O(L), even when sets are empty. A representation that permits a binary count of exponentially many omitted empty sets is a DIFFERENT compressed input model and is not used here.

Cases N=0, m<2, K<N, K>=mN are decidable directly (with the empty-universe convention specified by the source language). Invalid encodings and noncovering lists are rejected by the source-language verifier. A total many-one reduction can send each directly decided case to a fixed valid yes- or no-instance of the target language. For example, use the same two-type star and an input binary cell tree with two distinct terminal types: its score is zero, so threshold zero is yes. A fixed no-instance with nonnegative threshold zero is the three-type star and a binary tree whose two-leaf cherry has types a,b and whose other leaf has type c: its unique internal labels yield total score one. These instances have no polytomy, or can be replaced by fixed constant-size examples with one polytomy if that is required by the precise restricted language. The NP-hard nontrivial branch uses N>0, m>=2 and N<=K<=mN, exactly as in the source-only theorem.

For the restricted target with exactly one root polytomy, fixed yes/no examples can both use three composite binary blocks. For yes, use the two-type star S={a,b} and give each block one a cell and one b cell: every internal descendant set is S, so threshold zero is yes. For no, use the three-type star S={a,b,c} and give the three blocks types {a,b}, {a,b}, {a,c}, respectively: each fixed block root alone contributes one, so threshold zero is no. Every terminal type occurs, every internal vertex remains mixed and every label is forced to S. No negative threshold, missing terminal type or infeasible labeling is needed.

## 2. Output format and polynomial bounds

Assign terminal identifiers by disjoint tagged ranges for the N original types, H=mN+1 private types and two markers. Thus s=|S|=N+mN+3. Assign distinct cell identifiers by pairs (block identifier, terminal identifier). The root has m+1 indexed child blocks; each block is a fixed binary comb on its explicit cell list. The differentiation graph is the explicit star with s+1 vertices and s edges. All sampling weights are one. The fixed lambda is not part of the reduction's varying input, and all compatible edge-resolution costs are zero.

The source-only companion provides proposed bounds valid for every joining tree:

- s=N+mN+3;
- every block has at most s cells;
- every full refined cell tree has at most (m+1)s leaves;
- its number of vertices plus one is at most 2(m+1)s;
- all cell identifiers are distinct although terminal type labels may repeat across blocks.

These are deliberately loose bounds. They imply O(L^3) vertices using the explicit source encoding. Each cell/type/block identifier needs O(log(L+2)) bits. A pointer/list tree encoding and the explicit star graph therefore have polynomial output bit length. Even encoding every potency vertex by an s-bit vector remains polynomial.

The construction uses explicit loops over N, m, H and the listed memberships, writes the fixed block combs and star edges, and computes each fixed-block descendant set bottom-up. With s-bit type masks, one union or difference costs O(s) elementary bit operations. The fixed cost C0 is a sum of at most (m+1)s terms each at most s, so C0<=(m+1)s^2. The threshold gamma=C0+K-N is nonnegative on the nontrivial branch, bounded by (m+1)s^2+mN, and has polynomial bit length. Integer addition/subtraction and mask cardinality can be performed in polynomial bit time. These statements provide explicit size/time bounds; they are not a claim that a Lean complexity library has checked them.

## 3. Exact target certificate, not an ordering-only substitute

For the constructed instance a certificate is any rooted full binary joining tree on the m+1 block identifiers, with each identifier appearing exactly once. It may be balanced, caterpillar, or any other topology. Grafting the immutable block trees yields exactly the binary refinements of the input's sole root polytomy. This is the semantic correspondence still needing a formal representation theorem if the external problem is encoded through edge contractions or clade preservation instead of a direct refinement witness.

The checker:

1. Parses the proposed tree and verifies full binarity, a unique root, connectivity and acyclicity.
2. Checks that the joining leaves are exactly the m+1 block identifiers, without repetition.
3. Retains all fixed block topologies and distinct cell identifiers. It does not refine inside an already binary block or change the observations.
4. Computes every joining descendant-type mask by union of the two child masks.
5. Sums C0 plus s minus each joining descendant-mask cardinality and compares to gamma.

There are m joining internal vertices. This certificate and checker are polynomial size/time in the explicit input. The source-only `CartaStarRefinementDecision` additionally quantifies compatible cell-state labelings and proves proposed equality to this score, rather than silently removing label optimization. The mixed-descendant condition forces every internal state to S; every feasible edge is self or direct in the star, so resolution terms vanish for all lambda.

For the general explicitly supplied differentiation DAG and rational weights, the earlier full proof gives the more general NP checker: certify the full binary refinement and a state label at each lineage vertex, check refinement preservation and reachability, compute all descendant masks and sum the rational local/edge terms. The number of rational additions is polynomial, and the bit length of a common-denominator product is bounded by the sum of input denominator bit lengths. Arbitrary real-number oracle weights are not included in the input language.

## 4. Both directions and complexity dependency

On the nontrivial branch the exact finite equivalence is:

MSSC has an ordering of cost <=K if and only if the constructed cell-tree instance has some binary refinement and compatible labeling with D_lambda<=C0+K-N.

The forward map is anchor-first. The reverse implication starts with an arbitrary binary refinement, uses the no-more-expensive caterpillar exchange, excludes a late anchor by its H penalty and the threshold bound, swaps the first two positions if needed, and extracts a valid MSSC ordering. These are the proposed source terms `fullReductionClaim` and `full_carta_star_reduction`; neither has been elaborated.

The formal complexity endpoint still needs all of the following connected to one specific encoding and cost model: the source-language definition, an attributed formal MSSC NP-hardness theorem, a total polynomial-time constructor, the external refinement-semantics equivalence, and the polynomial target checker. A hand proof plus an unelaborated semantic equivalence does not instantiate that entire interface. No formal NP-completeness certificate is claimed.

The classical hardness dependency is Feige, Lovasz and Tetali, *Approximating Min Sum Set Cover*, Algorithmica 40, 219-234 (2004), DOI https://doi.org/10.1007/s00453-004-1110-5 . The author-hosted primary manuscript is https://tetali.math.gatech.edu/PUBLIS/mssc_final.pdf . Their hardness result is prior work; no new proof or originality claim for MSSC hardness is asserted here.
