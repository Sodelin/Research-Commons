# Galled does not mean one-hybrid blobs: an admitted source correction

31 October 2026. Own attributed source-definition audit and explicit hand construction: **dot, AI-assisted research**. The issue arose while reviewing the Claude Code / Full Pro candidate-cover and conditional outermost-gall work. Those source authors retain attribution for their results. This note concerns only a proposed source-class implication; it is not a new identifiability theorem, a novelty claim, a formal proof or an original G4 counterexample.

## Conclusion

The original admitted binary rooted-LSA, outer-labelled planar, cut-child galled class does **not** imply

> **G-simple:** every retained non-two-port blob is a simple cycle with exactly one hybrid.

A strict four-taxon source with a nonroot three-port, two-hybrid blob is given below. It also satisfies the per-hybrid ordinary-detour version of galledness. Thus G-simple must remain an additional hypothesis, or be replaced by a different proved source-coverage argument; it cannot be removed by interpreting the word “galled” as “level one.”

This preserves the public [no-upper-taxa simple-main-gall theorem](https://github.com/Sodelin/Research-Commons/blob/09a7b2ccdf6df82a2668d19f2993479ff22a4016/research/2026-10-31-g4-no-upper-taxa-core-review/DERIVATION-AND-REVIEW.md) and the source-scoped candidate-cover argument. Neither claimed arbitrary multi-hybrid core recovery. The conditional outermost composition is not refuted at its stated G-simple scope. No claim is made that G-simple is necessary for every possible wider identification theorem.

## 1. Exact registered source, not terminology

The [original G4 compiler, §1.1](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md) retains finite binary directed sources, root as lowest stable ancestor of all taxa, outer-labelled planarity, a cut child edge at every hybrid, n≥4, strictly positive finite lengths and interior inheritance weights. Section4.1 bounds a nonroot p-port blob by p−1 hybrids. It concludes “parallel-arm bigon” only for a nontrivial TWO-port blob; it does not conclude that a branching blob has one hybrid. Original protected IDs and admitted bridge-slot conditions in §§1.2/4.2 remain unchanged.

The source class is pinned in the accepted [all-level structural audit, §1 and §2.1](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/cba23504ec7c63936ab60e5c3beb65d296c2e9c5/research/nanuq-all-level-2026-09-29/ALL-LEVEL-STRUCTURAL-AUDIT.md). Its primary reference defines galledness by a cycle through each hybrid's two incoming edges with no other hybrid edges; it does not require distinct such cycles to be disjoint. The primary paper explicitly treats strictly level-two examples. See [Holtgrefe et al., Definitions2.1–2.4 and Figure2](https://link.springer.com/article/10.1007/s11538-025-01549-4).

The accepted [all-level proof, §1](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md) permits k hybrids and k bounded faces in a blob. Its one-hybrid-per-bounded-face assertion is NOT one hybrid per blob: different bounded faces may share ordinary edges. This distinction is exactly visible in the example below.

## 2. Explicit four-taxon source

Use distinct internal vertices rho,s,v,p,q,h1,h2 and distinct taxon leaves A,B,C,D. The complete directed edge list is

    rho→v, rho→s, s→C, s→D,
    v→p, v→h1, p→q, p→h2, q→h1, q→h2,
    h1→A, h2→B.

Every edge is a separate original edge. Assign pair survival1/2 to every finite population edge and inheritance weight1/2 at each hybrid. Above rho use the original unbounded ordinary ancestral population. Thus all finite population lengths equal log2>0 and all inheritance weights are strictly interior. Natural independent/current-lineage and common routing may both be defined on the SAME physical tuple; no observational equality between distinct sources is claimed.

### Binary degrees and acyclicity

rho has degree(0,2); s,v,p,q have degree(1,2); h1,h2 have degree(2,1); A,B,C,D have degree(1,0). A topological ordering is rho, then s and v, then p, then q, then h1,h2, then the leaves (C,D may be placed earlier after s). Hence the source is finite and acyclic, with unique root and four original taxa.

### Root-LSA and cut children

The root's v side contains A,B and its s side contains C,D. No vertex below rho is ancestral to all four taxa, so rho is their least stable ancestor. Both root edges are cuts. Each hybrid's only outgoing edge is its pendant edge to A or B, hence is a cut edge. There is no trivalent hybrid with an internal noncut child, no root relocation and no invisible extra taxon.

### One nonroot three-port blob with two hybrids

The internal subgraph on {v,p,q,h1,h2} has six edges:

    vp, vh1, pq, ph2, qh1, qh2.

Every one lies on an undirected cycle, and the graph is connected, so it has no bridge. Its outside incident edges rho→v, h1→A and h2→B are bridges. It is therefore one maximal nonroot blob with exactly three ports and two hybrids. Its cyclomatic number is6−5+1=2. In particular it is neither a two-port word/bigon nor a simple one-hybrid cycle. It attains, rather than violates, the compiler's p−1 hybrid bound at p=3.

### Galledness with original edge directions retained

For h1, its incoming edges v→h1 and q→h1 lie on the undirected cycle

    h1–v–p–q–h1.

The other edges v→p and p→q are ordinary tree edges. For h2, its incoming edges p→h2 and q→h2 lie on

    h2–p–q–h2,

whose remaining edge p→q is ordinary. Thus each hybrid has its required cycle containing no OTHER hybrid edges. Equivalently the ordinary parent detours are v–p–q for h1 and p–q for h2; neither detour visits its hybrid. The two cycles share the ordinary edge p→q, which is permitted by this galled definition. No hybrid is ancestral to the other within the blob.

### Outer-labelled planar embedding and rooted partner

Draw the simple outer polygon in cyclic order

    v, p, h2, q, h1

and draw pq as its interior chord. Its boundary edges and chord are exactly the six blob edges. Attach rho and the C/D rooted cherry outward at v, A outward at h1, and B outward at h2, using disjoint exterior sectors. There are no crossings and every taxon is on the unbounded face. The two bounded faces are the h1 quadrilateral and the h2 triangle, each with exactly one hybrid, although they belong to the SAME blob.

This is already a directed rooted partner with the required binary/LSA properties. Retaining only hybrid-edge directions and suppressing rho gives an admitted semi-directed source: the two root bridges become the bridge v–s; the two-hybrid blob remains intact. No direction or original edge is silently changed in the rooted source used for the stochastic model.

These checks establish the source-class counterexample to G-simple by hand. They are not a fresh graph-engine or Lean certificate.

## 3. The obstruction also fits arbitrary cut-component interiors

The broader selected-main-gall class allows arbitrary admitted cut-component interiors. To exhibit the same issue THERE, retain the entry-v two-taxon component above (its six blob edges and h1→A,h2→B), and attach it below the hybrid H0 of a separate simple main triangle. Use a new root R, main top V, side vertex W, side taxon B0 and external taxon C0, with edges

    R→V, R→C0,
    V→W, W→H0, V→H0,
    W→B0, H0→v.

The four original taxa are A,B,B0,C0. Again set every finite survival and coin to1/2. The new hybrid H0 has the cut child H0→v; all old child cuts remain cuts. R is LSA because C0 is on its other root side. The two blobs are joined by a bridge, so their outward embeddings combine without crossings and all four leaves remain exterior.

The selected main gall is simple, nonroot and has no upper taxa, yet its H-descendant cut component contains the admitted two-hybrid three-port blob. This is allowed by the public simple-main theorem's arbitrary-interior clause and is NOT a counterexample to that theorem. It shows why a predicate applying to EVERY retained blob cannot be inferred even from the selected-main class. In this nested example the OUTERMOST main blob is simple, so it also does not prove that every weaker sufficient outermost hypothesis fails. The first example already shows that a non-simple blob may itself be outermost on a two-cut-root side.

## 4. Consequence for the original G4 route

The finite observable orientation-graph candidate cover can remain valid in its selected-main/tree-spine class, and the conditional composition under explicit G-simple can remain valid. What fails is the automatic extension of that composition to ALL registered galled sources using a nonexistent general simple-blob implication.

The correct outstanding obligation is an actual-source classification/decoder covering multi-hybrid retained blobs, or another proved coverage reduction preserving the original full observations and physical source class. Merely renaming a multi-hybrid blob as several independent one-hybrid words would lose their shared ordinary region and joint lineage histories. The six-edge blob is not an eligible bridge slot on which such a replacement has been proved.

This graph is not an observational ambiguity, does not furnish COMMON-bad rivals, and is not a negative solution of G4. Existing W3/fixed-port/no-upper-taxa results, known upper-I acquisition and original G3/G4 master scopes remain unchanged. No additional tree-child restriction is present in the cited original class; adding one or imposing level one would be a new subclass, not a repair of the original all-rival quantifier.
