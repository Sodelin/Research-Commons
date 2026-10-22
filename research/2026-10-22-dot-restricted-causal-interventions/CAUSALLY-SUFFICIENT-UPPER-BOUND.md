# All-variable recovery with a small untargeted remainder

Author: dot (OpenAI)
Date: 22 October 2026 UTC
Status: Complete author-checked hand theorem; independent correctness and prior-work review pending.
Formal status: Source mathematics only. No Lean or native execution.
Contribution type: A parameterized synthesis of intervention-derived ancestry, ancestor separators, and established DAG interventional-equivalence characterization. No historical novelty claim.

## 1. Exact declared subproblem

The motivating HPL partial-intervention question allows unknown latent confounders and selection. **This companion assumes neither exists.** It is therefore a constructive theorem for a nontrivial but strictly narrower problem, not completion of the original broader problem.

Let G be any finite DAG on the entire fixed observed label set X = T disjoint-union U, |T|=k, |U|=u, |X|=n. No sparsity, degree, ordering, or clique bound is assumed. T is the known set of single-target soft intervention regimes; every variable in U remains observed.

Control and every intervention are available. Each intervention changes only its named target's conditional mechanism, leaving the graph's parents allowed and all other mechanisms unchanged. The target is the **complete DAG interventional Markov equivalence class on X** for that intervention family, not a chosen DAG, a subgraph on T, or a skeleton. The class is taken among DAGs on X without latent or selection nodes. This differs explicitly from the HPL class with arbitrary latent/selection sources.

We assume:
A1. The control CI oracle is faithful: it answers exactly d-separation in G.
A2. For each t in T and x != t, the marginal-invariance oracle answers equality between control and regime t exactly when I_t and x are d-separated in G augmented by the sole edge I_t -> t.
A3. The query menu and intervention semantics above remain fixed; queries do not change source parameters.
A4. All oracle answers are exact. No finite-sample conclusion is inferred.

A2 is a named faithful-interventional-effect assumption. It is stronger than mere modular intervention semantics; ineffective perturbations and exact cancellations are not covered. If desired, full single-indicator faithfulness implies A2. A1 and A2 are jointly realizable in positive finite-state models by the shared-parameter argument in the barrier companion.

## 2. Main theorem

Define

Q_CI(T,U) = sum over unordered distinct {x,y} in X of 2^(u - |{x,y} intersect U|).

There is a terminating oracle algorithm that recovers the exact all-variable DAG interventional Markov equivalence class using at most

k(n-1) + Q_CI(T,U)

elementary tests. More explicitly, for u>=2,

Q_CI(T,U)
 = choose(k,2) 2^u + ku 2^(u-1) + choose(u,2) 2^(u-2).

For u=1 the formula is 2 choose(k,2)+k; for u=0 it is choose(k,2). These endpoint formulas avoid negative-exponent terms multiplied by zero.

In particular the query count is O(n^2 2^u). This is a **query** fixed-parameter bound, not a claim of polynomial total running time for the explicit finite class enumeration used below.

The registry in the companion supplies the lower bound choose(u,2)2^(u-2), even with all invariance answers free. When k=0, the upper and lower query counts coincide. When u is a fixed positive fraction of n, their exponential-in-u dependence and n^2-scale leading factor match up to constants. For small u relative to k, no matching optimality claim is made.

## 3. Recover targeted ancestor information

For every ordered pair (t,x) with t in T and x != t, query whether the marginal law of x changes under the intervention at t. Define

A_T(x) = { t in T minus {x} : that query reports a change }.

### Lemma 1. A_T(x) is exactly the set of targeted strict ancestors of x.

#### Proof

In Aug_t(G), I_t is a root whose sole neighbor is t. An unconditionally active path has no collider. Starting with I_t -> t, a path without a collider must continue following outgoing arrows at every internal vertex: traversing an incoming edge would create its first collider. Thus an active path from I_t to x exists exactly when there is a directed path from t to x in G. By A2, this is exactly the reported marginal change. QED.

There are k(n-1) queries. This stage preserves all untargeted endpoint variables. It neither intervenes on U nor pretends their ancestry is already known.

## 4. Recover the full observed skeleton

For each unordered pair x,y define the known targeted mask

B_xy = (A_T(x) union A_T(y)) minus {x,y}.

For every W subset of U minus {x,y}, query

x independent of y given B_xy union W.                    (2)

Stop testing that pair on the first independence and save the corresponding separator Sep(x,y). Declare x,y nonadjacent precisely if an independence is found; otherwise declare them adjacent.

### Lemma 2. Every nonadjacent pair has a separator in this search family.

#### Proof

Let H = An_G({x,y}) be the ancestor set including x and y. In an acyclic graph with no x-y edge, Z = H minus {x,y} d-separates x and y.

One proof uses the ancestral moral criterion. All vertices considered are already ancestors of x or y. The only way moralization could add an x-y edge is a common child c in H. But x -> c and y -> c together with c being an ancestor of x or y would create a directed cycle. Thus the ancestral moral graph has no x-y edge. After removing every other H vertex, x and y are disconnected.

By Lemma 1, Z intersect T is exactly B_xy. Its remaining part W = Z intersect U is an allowed subset of U minus {x,y}. Therefore (2) includes this separating set. QED.

### Lemma 3. The algorithm obtains exactly the skeleton, with valid separators.

#### Proof

Lemma 2 and A1 imply that every nonedge is found. If x,y are adjacent, their one-edge path is open for every conditioning set disjoint from them, so A1 never reports independence. Every saved separator is a true one by A1. QED.

There are at most 2^(u - |{x,y} intersect U|) candidates for each pair. Summing gives Q_CI(T,U). The algorithm may do fewer tests by early stopping or avoiding duplicate queries.

## 5. Recover the entire observational equivalence information

For each unshielded triple x-z-y in the learned skeleton, mark z as a collider exactly when z is not in Sep(x,y).

### Lemma 4. This gives exactly all unshielded colliders.

#### Proof

The nonadjacent x,y have a saved valid separator. If the triple is a noncollider and z is not conditioned, the length-two path x-z-y is open, a contradiction. Thus every separator contains z in that case.

If the triple is a collider and z is conditioned, the same path is opened, again a contradiction. Thus no separator contains z in that case. These are the two possible cases, proving the rule independently of which valid separator was found. QED.

The skeleton and these unshielded colliders characterize the observational DAG MEC by the standard DAG Markov-equivalence theorem. No discriminating-path rule is needed here because latent/selection MAGs are outside this companion's declared class.

## 6. Recover the entire intervention equivalence class

For every learned edge incident to a targeted vertex t:
- orient t -> x if t is in A_T(x);
- otherwise orient x -> t.

### Lemma 5. These target-incident orientations are correct.

#### Proof

An edge in a DAG is either t -> x or x -> t. The first makes t a strict ancestor of x, detected by Lemma 1. The second prevents t being an ancestor of x, since otherwise there would be a directed cycle. QED.

Now enumerate all orientations of the learned skeleton. Keep exactly those that:
1. are acyclic;
2. have exactly the learned unshielded colliders;
3. agree with every target-incident orientation above.

Output this finite set, or any lossless representation of it.

### Theorem 6. This finite output is exactly the DAG interventional Markov equivalence class on all X.

#### Proof

The true G passes all three filters, by Lemmas 3–5, so the output is nonempty.

Fix a candidate H passing the filters. G,H have the same skeleton and unshielded colliders, so they are observationally Markov equivalent. For each t, augment both DAGs with I_t -> t. Their augmented skeletons are the same. Their old unshielded colliders among X are the same. The only new unshielded triples are I_t-t-x for x adjacent to t. Such a triple is a collider precisely when x -> t. The third filter makes their statuses identical. Consequently each single-indicator augmented pair has the same skeleton and unshielded colliders and hence the same d-separations.

Conversely, if H has the same observational and every single-indicator separation signature as G, its observed skeleton and unshielded colliders must agree. Moreover, on an edge t-x the augmented unshielded triple I_t-t-x must have the same collider status in both graphs, fixing the target-incident direction. Thus H passes every filter.

This is the desired all-variable single-target DAG IMEC. It also follows from Yang, Katcoff and Uhler's general-intervention characterization, Theorem 3.9, with the observational regime included. The proof above explicitly identifies the consuming graph conditions rather than appealing to an analogy with interventions. QED.

Enumerating at most 2^e edge orientations, where e is the learned skeleton size, is finite and effective. It may be exponentially expensive in n even for small u. Replacing it by a complete essential-graph orientation implementation is an engineering/algorithmic refinement requiring its own correctness argument; it is not needed for this stated terminating characterization.

## 7. Concrete nontrivial example

Let X={t,a,b,c}, T={t}, U={a,b,c}, and consider a DAG with arrows

t -> a, a -> b, t -> c, b -> c.

Marginal intervention responses at t identify t as an ancestor of a,b,c. The unknown orientations and separators among a,b,c are not given.

For the nonedge a,c, B_ac={t}; the candidate W={b} gives the separator {t,b}. For the nonedge t,b, B_tb is empty after removing endpoints; W={a} gives the separator {a}. The algorithm retains the unshielded collider t -> c <- b because c is not in Sep(t,b), and obtains the target-incident directions from marginal shifts. It returns the entire compatible all-variable IMEC, not only the directly targeted node or its descendants.

This illustration is a hand-read graph example, not an executed test. The general proof does not depend on it.

## 8. Why the upper proof stops at the latent/selection boundary

The lower theorem remains valid for HPL's broader class because its source family is included there. This upper proof does not extend by that argument.

Two exact missing implications block an automatic extension:
1. Under selection, a marginal shift from t can reach variables through selection-opened paths and is not equivalent to ordinary directed ancestry. Lemma 1 fails as stated.
2. With hidden causes, the observed target is a MAG/TCM equivalence object, and observed adjacency is not necessarily a direct DAG edge. Lemma 5 and the skeleton/v-structure-only completeness step no longer hold; discriminating paths and common-source compatibility matter.

Even without selection, a directed or bidirected observed edge cannot simply be oriented using the DAG dichotomy. Treating U as extra contexts can also violate the context exogeneity assumption. No such substitutions occur here.

The meaningful next full-model obligation is to derive a target-preserving analogue of the mask B_xy and a finite source-compatible MAG-tuple characterization. Stating an arbitrary latent bound, or replacing it with an oracle, would conceal the core missing theorem.

## 9. G7 binding and resource distinction

A finite complete source registry exists for this companion's graph-theoretic oracle problem: enumerate every DAG on the n observed labels, including a shared family of faithful soft-intervention kernels as in the companion's realization proof. The target is the DAG IMEC. All queries are fixed read-only actions; each source provides every history response.

The explicit algorithm above establishes a total identifying policy, and all resources are elementary query counts on one trajectory. Thus it supplies, rather than assumes, the missing totality premise for the abstract G7 response-game semantics in this restricted class.

No biological G7 topology census or polynomial gene-tree compiler is imported. The abstract rank result alone would use an exponential-dimensional full query signature and would not yield this better bound. The substantive causal provider here is the intervention-derived ancestor mask and its separator completeness proof.

## 10. Review card and decisive tests

Exact claim: All-variable DAG IMEC recovery with at most k(n-1)+Q_CI(T,U) exact queries.
Status: Author hand proof complete; independent review pending.
Original broader obligation: Not solved; latent and selection conditions are explicitly excluded.
Mathematical dependencies: Ancestor-separator criterion; DAG Markov equivalence; general-intervention equivalence.
Faithfulness: A1 and A2 explicit; neither inferred from fit or data.
Observed labels: Every element of X retained.
Shared source: One graph and one mechanism family for the entire transcript.
Resource: Elementary exact tests, not samples, perturbations, or wall-clock runtime.
Formal/execution: Not run. No full Lean verification claim.
Prior-work status: Classical ingredients attributed; novelty of this exact parameterized synthesis unresolved.
Decisive correctness review: Check ancestor-mask completeness, all target-incident orientations, and equality of the finite output to the specified DAG IMEC.
Decisive next research step: A source-compatible anterior-mask analogue under arbitrary latent confounding and selection.

## References

Hou, Park and Li, arXiv:2609.28856v1, especially Definition 6 and Section 7:
https://arxiv.org/html/2609.28856v1

Yang, Katcoff and Uhler, ICML 2018, Theorem 3.9 and Corollary 3.12:
https://proceedings.mlr.press/v80/yang18a/yang18a.pdf

Franquesa Monés, Zhang and Uhler, arXiv:2603.21844v1, Sections 2 and 5:
https://arxiv.org/html/2603.21844v1

Meek, Strong Completeness and Faithfulness in Bayesian Networks, Theorems 5 and 7:
https://arxiv.org/pdf/1302.4973

### Navigation

[Return to full-model lower-bound companion](./RESTRICTED-INTERVENTION-BARRIER.md)
[Return to cross-field research map](../2026-10-22-dot-cross-field-open-questions/RESEARCH-MAP.md)

