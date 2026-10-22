# A finite common-source registry with latent variables and selection

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: Scoped independent coordinating-context hand-review PASS received 22 October 2026; historical-priority review remains open. See HAND-REVIEW-2026-10-22.md.
Formal status: No runtime execution, statistical experiment, or Lean verification.
Attribution: A source-compression synthesis using classical latent projection, selected MAG semantics, and discrete faithfulness. No historical-priority claim is made. Stable mixed/summary graphs and earlier soft-intervention completion algorithms are relevant prior work, not displaced by this note.

## 1. Exact result and scope

Let X=T disjoint-union U be the fixed observed system labels, n=|X|, k=|T|, u=|U|. Consider the full HPL SIS source class: arbitrary finite latent L, arbitrary finite **selection sinks** S, and separate soft-intervention augmentations I_t -> t for the named t in T. Selection mechanisms are unchanged across regimes. The source need not have a supplied bound on |L| or |S|. Context removal and the strong exact CI/invariance biconditionals are exactly those in LATENT-SELECTION-IMEC-CERTIFICATE.md.

The target remains the full selected, latent-variable target

TCMclass(D) = { TCM(D',T) : D' approximately_T D }.

Every observed label, including every untargetable one, is retained. The relation is HPL's separate-indicator CI/invariance equivalence, not equality of whole numerical laws.

**Main theorem.** There is a complete finite registry of common SIS sources preserving all observed CI responses, every separate named-indicator response, and each source's actual marked base and augmented MAGs. One may take at most

R(n) = 2^n 96^choose(n,2)

registry entries. Each is a DAG with at most n+4 choose(n,2) selection sinks and 9 choose(n,2) latent roots. Consequently, after the B(n,k,u)=O(n^2 2^u) elementary queries of the certificate manuscript, a terminating finite procedure lists exactly TCMclass(D).

This is not a polynomial-total-time or practical enumeration algorithm. It is not a statistical sample bound, a full-law equivalence theorem, a hard-intervention result, a proof of historical novelty, or a solution under HPL's weaker minimal statistical assumptions. Full-coverage identification and the original quadratic query result remain HPL's prior work.

## 2. First project latents, but retain selection nodes

Given the SIS DAG D on X union L union S, form the ordinary bow-permitting latent-projection ADMG H on X union S, marginalizing only L. A directed edge is witnessed by a directed path with latent internal nodes; a bidirected edge by an into-both-endpoints collider-free path with latent internal nodes. A directed and a bidirected edge may coexist on one pair.

Richardson–Evans–Robins–Shpitser (2023), Proposition 1 and Supplement A.3–A.4, provide the standard equivalence

A d-separated B | Z union S in D
iff A m-separated B | Z union S in H.                         (1)

Here A,B,Z are disjoint subsets of X. This theorem is attributed in that source to the latent-projection tradition of Verma and Pearl; it is not a new result of this note. Directed observed ancestry is also preserved, by splitting or expanding directed paths at retained vertices.

Since every original selection node is a sink, no directed edge of H leaves S. In particular there are no directed edges between selection nodes. Every edge incidence at a selection node is an arrowhead: X -> S, X <-> S, or S <-> S. The directed part H_X of H restricted to X is acyclic. Bidirected edges on X are retained too; H_X denotes the entire bow-permitting induced ADMG unless directed reachability is explicitly specified.

## 3. A finite description of all selected paths

Consider the connected components c of the bidirected subgraph induced by S. Isolated selection vertices count as components. Define their two boundary sets

P_c = { x in X : x -> s for some s in c },
B_c = { x in X : x <-> s for some s in c }.

These sets are kept separate and may overlap. Set F=union_c P_c. For distinct x,y, record each ordered pair of endpoint marks (alpha,beta) in {tail,head}^2 for which a component c supports x with mark alpha and y with mark beta: tail means membership in P_c, head membership in B_c. Call the resulting labeled relation V. It has at most four marked possibilities for each unordered pair. Endpoints are ordered by a fixed label ordering when encoding V.

The triple Q=(H_X,F,V) is a **description**, not a MAG and not a causal DAG on X. In particular a virtual marked pair is not asserted to be a causal edge. The separate F flag is indispensable even when a selection component has only one observed boundary vertex.

### Lemma 1. Collider activation and selection ancestry

For Z subset X,

An_H(Z union S) intersect X = An_HX(Z union F),                (2)

where ancestry is directed and includes the vertices themselves. Also

An_H(S) intersect X = An_HX(F).                               (3)

#### Proof

A directed path between observed vertices cannot enter S, since S has no outgoing directed edges. Such paths stay in H_X. A directed path from an observed vertex to S first enters S at its final edge x -> s, for some x in F. Conversely any directed path to x in F extends through one such x -> s. This proves (2) and (3). In particular neither B_c membership nor mere selected dependence is a substitute for ancestry. QED.

### Lemma 2. Selected path criterion determined by Q

For distinct a,b in X and Z subset X minus {a,b}, m-connection given Z union S is determined solely by Q. More explicitly it is equivalent to the existence of a sequence of distinct observed vertices from a to b whose consecutive links are either actual H_X edges or marked virtual pairs from V, and such that:

- each internal observed noncollider is outside Z;
- each internal observed collider belongs to An_HX(Z union F).

Collider status uses the chosen endpoint marks of the actual or virtual links. Multiple choices on the same pair are allowed, and one is fixed for each link in the sequence.

#### Proof, forward direction

Take a simple m-connecting path in H. Each maximal consecutive block of selection vertices has only bidirected edges internally. Its distinct observed endpoints therefore belong to the boundary of one component, with the endpoint marks recorded by V. Contract each such block to its corresponding marked virtual link. Other links already lie in H_X.

The retained observed subsequence has no repeated vertex because the original path was simple. Its observed local marks, hence its collider/noncollider statuses, are unchanged. Noncolliders remain outside Z. Its colliders satisfy the asserted ancestor condition by (2). The contracted sequence therefore meets the criterion.

#### Proof, reverse direction and loop reduction

Take a distinct-observed-vertex sequence satisfying the criterion. For each virtual link x,y, choose a component witnessing its two marks. Choose one boundary edge at x, one at y, and a simple bidirected path inside that component between their selection endpoints; if the endpoints coincide the internal component path has length zero. This gives an x-to-y path with selection-only interior. Expand every virtual link this way.

The resulting walk has **no repeated observed vertices**: expansions add selection vertices only, and its original observed sequence was distinct. Its selection vertices may repeat across different expansions. Every occurrence of a selection vertex is a collider, since every incidence there is an arrowhead, and is active because all S are conditioned. Every surviving observed collider is active by (2), and every observed noncollider is outside Z.

To obtain a simple path, if a selection vertex s occurs twice, remove the segment from its first occurrence to the chosen later occurrence, identifying those occurrences. The retained incidence entering s and the retained incidence leaving s both have arrowheads at s. Thus s remains an active collider. Other surviving vertices retain exactly their former two incidences, and hence their former statuses and activation. The endpoints are observed and cannot be removed by this operation. The walk strictly shortens. Repeating eliminates every repetition, since only selection vertices could repeat. The resulting simple path is m-connecting given Z union S. This proves the reverse implication without assuming an arbitrary active-walk theorem. QED.

The proof applies to endpoint sets by applying it to every pair of endpoints. It also shows why keeping only one independent selected MAG for each regime would be insufficient: Q retains a shared underlying directed structure and selection ancestry information.

## 4. An explicit common canonical source

Call a triple Q=(H_X,F,V) admissible if H_X is any bow-permitting ADMG on X with acyclic directed part, F subset X, V contains any subset of the four marked possibilities on each distinct pair, and each tail incidence of V is at a vertex in F. No further constraint is needed for the construction below. Every Q extracted from a source in Section 3 is admissible.

Construct a mixed graph K(Q) on X and new selected vertices as follows:

1. Retain H_X exactly.
2. For each x in F, add a distinct selection sink s_x and x -> s_x. This records all singleton selection-ancestry flags.
3. For each marked pair (x,y;alpha,beta) in V, add its own distinct selection sink s_v. Connect x to s_v by x -> s_v if alpha is tail and x <-> s_v if alpha is head. Do the analogous operation for y and beta.
4. Add no edges between selection vertices.

K has at most |F|+|V| <= n+4 choose(n,2) selection sinks. Its selected components are singleton vertices. The marked-pair relation extracted from K is exactly V: each two-boundary selected vertex contributes its designated pair with its designated endpoint marks, and each one-boundary selected vertex contributes no distinct pair. The direct-parent flag extracted from K is exactly F: every x in F has its singleton child, and admissibility prevents a virtual tail outside F. Its observed subgraph is exactly H_X.

Replace every bidirected edge of K by a distinct new latent root with arrows to its two endpoints; keep every directed edge. Denote the resulting DAG C(Q). These roots have no incoming edges, selection vertices remain sinks, and the directed observed part is acyclic. Thus C(Q) is an admissible SIS DAG.

There are at most choose(n,2) bidirected edges inside H_X and at most 2|V| <= 8 choose(n,2) bidirected observed-selection edges. Hence C(Q) has at most 9 choose(n,2) latent roots.

### Lemma 3. The projection of the canonical DAG is K(Q)

Latent-projecting the new roots from C(Q), while retaining X and its selection vertices, gives exactly K(Q).

#### Proof

No directed old-to-old path with latent internal vertices can enter a new root, so only retained directed edges project. A collider-free into-both-endpoints path with latent-only interior can contain only one new root: different roots have no connecting edge, and passing between them would require an old internal vertex. Such paths are exactly a <- l_ab -> b for the replaced bidirected edges. Bows are consequently preserved, not erased. QED.

### Theorem 4. Source compression preserves selected separation and ancestry

Let Q be extracted from D. Then D and C(Q) have identical separations on X given every Z union their respective selection sets, identical observed directed ancestry, and identical sets of observed ancestors of selection.

#### Proof

Use (1), Lemma 2, and Lemma 3. Both projected mixed graphs have the same Q, so the same selected m-connections. Directed observed ancestry is preserved by latent projection and equals the directed ancestry of the unchanged H_X. Ancestry to selection is exactly An_HX(F) by (3) for both graphs. QED.

Singletons are intentionally retained. For example a lone edge x -> s contributes no virtual pair, but makes x an ancestor of selection; omitting it could alter a MAG endpoint at x or at its intervention indicator. A B-only singleton contributes neither a virtual pair nor F, and can be discarded by the proved criterion, not by an informal assertion that selection is irrelevant.

## 5. All named soft interventions use this same source

For any observed t, let Aug_t add the fresh root I_t with sole edge I_t -> t. Ordinary latent projection retaining X union S union {I_t} commutes with this operation. Indeed a path from I_t to any different old vertex must pass through retained t internally, so it cannot create an extra latent-projection edge; old-to-old projection paths cannot use the fresh degree-one root internally. The only added projected edge is I_t -> t.

The selection components and all their boundary incidences are unchanged. In particular I_t lies in none of their P or B sets. The description on observed labels X union {I_t} is therefore exactly the old description with the edge I_t -> t added to H_X, no new virtual link, and no new direct-parent flag. Ancestors of selection may nevertheless include I_t through the path I_t -> t -> ... -> F, exactly as (3) requires.

Apply Lemmas 1–3 on this enlarged observed set. The previously constructed canonical source C(Q), augmented by I_t -> t, has the same enlarged description. Thus Theorem 4 holds simultaneously for D and C(Q) after every separate named augmentation, with **one fixed canonical SIS** serving all t. There is no Cartesian-product realizability assumption and no use of a single joint-indicator MAG.

### Corollary 5. Exact marked MAGs and TCMs are preserved

M_0(D)=M_0(C(Q)) and M_t(D)=M_t(C(Q)) for every t, as labeled marked graphs, not merely as Markov-equivalence classes. Therefore TCM(D,T)=TCM(C(Q),T).

#### Proof

MAG adjacency is nonseparability by every allowed observed conditioning set, so equal selected separations give equal skeletons. In the selected MAG of a DAG, the endpoint at a on an adjacent a,b pair is a tail exactly when a is an ancestor of b or of some selection node; otherwise it is an arrowhead. This is the standard selected MAG projection rule used by HPL and Richardson–Spirtes. Theorem 4 preserves both ancestry alternatives, also on each enlarged observed set by Section 5. Thus every endpoint mark agrees. Finally take the same union of separate slices and trim the same own-target edges. QED.

## 6. Fixed mechanisms faithful at the selected value

The structural registry suffices for the graphical decoder. For a registry of actual exact-oracle sources, however, one must not silently assume that ordinary faithfulness automatically holds within the particular selected slice S=1. We now prove existence of simultaneous strictly positive rational binary representatives, including this slice condition.

### Lemma 6. A nonseparation has a selected-slice polynomial witness

Fix any finite DAG G with binary variables and selection nodes S. If a,b are d-connected given Z union S, then in the positive binary DAG parameter space the assertion a independent b given Z,S=1 is contained in the zero set of a nonzero polynomial.

#### Proof

By Meek's discrete DAG faithfulness theorem, a positive binary model exists in which a and b are dependent given Z union S. Hence for some assignment z,s and endpoint values, a conditional-independence cross-product minor is nonzero. Independently relabel the two states at each selection variable so that this s becomes the all-one assignment. State relabeling preserves the DAG factorization and positivity. It gives a witness with a nonzero minor at S=1.

Joint probabilities and their marginals are polynomials in finite CPT parameters. Clear the strictly positive conditional denominators. The chosen nonzero minor at Z=z,S=1 is therefore a nonzero polynomial in those parameters. Selected conditional independence requires all such minors to vanish, in particular this one. QED.

The state relabeling is only used separately to prove that each polynomial is nonzero. It is not a different mechanism chosen in each final experiment.

### Lemma 7. One rational representative works across all regimes

For each canonical source C(Q), there exist base kernels and one soft replacement kernel per t in T, all strictly positive rational binary tables, such that the base selected CIs and every separate augmented selected CI agree exactly with their graph-separation signatures. One can also require ordinary base and regime faithfulness simultaneously.

#### Proof

Use a common open-cube parameter space consisting of all base CPTs, one free replacement CPT at each named target with the same parent set, and a free positive binary mixing probability for each separate indicator. Nontarget kernels, including selection and latent-root kernels, are shared unchanged across all regimes.

For each t, this parameter space maps onto the entire positive binary DAG parameter space for Aug_t(C(Q)): the two slices of t's CPT given I_t are its free base and replacement CPTs, other CPTs are free base tables, and the indicator probability is free. It likewise maps onto the whole parameter space of the base graph and each individual soft-replacement regime. These maps are coordinate selections or renamings and are polynomial and surjective.

For every graphically d-connected queried selected statement, choose the nonzero polynomial from Lemma 6 and pull it back by the appropriate surjection. Its pullback is nonzero. The same standard argument handles any desired ordinary faithfulness statements. There are finitely many graphs, regimes and statements. The product of their nonzero polynomials is nonzero. Its complement in the common positive parameter cube is a nonempty open set, and contains a rational point. Fix one such point once for all regimes. Graphically implied independences hold for every factorizing distribution, including in the positive selected slice, while all unwanted ones were excluded. QED.

For binary I_t with positive support, its selected conditional independence from x given Z is exactly equality of the selected x|Z conditional laws in its two regimes. Thus these representatives implement the stated soft-invariance oracle with unchanged nontarget mechanisms. Context can be absent, which satisfies HPL's context restrictions. This is an existence proof and a terminating rational-table enumeration specification, not a numerical model that was actually computed. It asserts equal oracle signatures and graph targets, not equal original numerical laws, nested constraints, or latent state spaces.

## 7. Complete registry and exact TCM listing

Enumerate H_X by independently choosing one of three directed states and presence/absence of a bidirected edge on each unordered pair, rejecting directed cycles. This gives at most 6^choose(n,2) candidates. Enumerate all 2^n choices of F and all 16^choose(n,2) choices of the four-mark relation V, rejecting any tail incidence outside F. The total is at most

6^choose(n,2) 2^n 16^choose(n,2) = R(n).

Every remaining triple has the explicit admissible source C(Q). Every arbitrary finite HPL SIS has an extracted admissible triple and, by Corollary 5, the same actual base/augmented MAGs and TCM as that canonical source. This proves registry completeness for the required response and target maps, not for all probability distributions.

After the certificate algorithm has answered its B(n,k,u) queries:

1. Enumerate all admissible triples and their canonical sources.
2. Compute the finite base MAG and each separate augmented MAG of each canonical source.
3. Test them against the certificate's finite saved-skeleton and separator predicates.
4. Collect the TCM of every passing common source, deduplicating identical finite labeled graphs.

### Theorem 8. The returned list is exactly TCMclass(D)

#### Proof

The registry is finite and each construction, reachability, separation and certificate check is finite, so the algorithm terminates. A passing canonical source lies in D's full IMEC by the certificate theorem. It is an admissible source, including a faithful fixed-mechanism probability representative by Lemma 7. Therefore its TCM is in TCMclass(D), proving soundness.

Conversely take any finite source D' in that IMEC with arbitrary hidden and selection sizes. Extract its Q'. It occurs in the registry. Corollary 5 gives identical base and separate augmented MAGs and identical marked TCM for D' and C(Q'). Hence C(Q') passes the same certificate and contributes exactly D's requested rival TCM. Every member of TCMclass(D) is collected. QED.

The result closes the certificate's explicit common-source realization obligation under its exact oracle assumptions. It does not make the equivalence class a singleton: partial coverage can leave multiple TCMs, as HPL and the lower companion show. It also does not remove the exponential elementary-query barrier in u or the finite but extremely large postprocessing.

## 8. Exact G7 adapter, not an analogy

The structural source map is D -> Q(D) -> C(Q(D)). Sections 4–5 preserve every allowed elementary response and the actual marked TCM. Lemma 7 provides actual probability representatives if the finite game carrier is required to contain them rather than structural signatures.

Use as actions the finite elementary CI and separate conditional-invariance predicates on the fixed named regimes, as responses their exact Boolean answers, as target the full TCM equivalence-class list, and as resource the remaining query count. One fixed source and fixed replacements determine the entire transcript. A query only reads a predicate; it is not identified with creating a new intervention. Repeated/reset observations and deletion of unused queries have the abstract G7 resource-game semantics already specified in the certificate manuscript.

The finite registry is now complete by proof rather than an assumed latent-size bound. A valid policy on it pulls back to all admitted original sources because both response and target commute with the source map. The constructed certificate policy followed by the exact decoder is target-homogeneous at every terminal history. This instantiates the accepted abstract G7 transcript/identification theorem. It does not instantiate the original biological polynomial compiler, does not provide noisy tests or arbitrary affine physical actions, and does not settle G4.

## 9. Prior work, unresolved priority, and boundaries

The decisive primitive is classical bow-preserving latent projection. Stable mixed/summary graphs already represent DAG independences after marginalization and conditioning; Sadeghi (2013) proves broad closure and representation results. Thus the finite selected graph-representation theme is not new. The present construction is written explicitly to preserve directed ancestry, ancestry to selection, and **every named separate soft-indicator augmentation through one common source**, which are the precise obligations needed by this packet. Historical priority of this particular normal form and parameterized query application has not been established.

Earlier latent soft-intervention equivalence is due to Kocaoglu and colleagues (2019). Zhou–Kocaoglu (ICML 2026) already provide exact common-source I-MAG realization and enumeration-based completion in a no-selection joint-augmentation domain. The full primary PDF and relevant proofs/algorithms have now been read; earlier abstract-only statements are superseded. HPL supplies the selected target and anterior/adjacency query identities. This note must be read as an attributed synthesis/candidate rather than a claim to originate these components. [The exact-claim reconciliation](PRIOR-WORK-EXACT-CLAIM-RECONCILIATION.md) proves why raw stable-graph representations and the unmodified no-selection realizability test do not automatically supply the selected named-root adapter, without asserting historical novelty.

No inference is made from this soft-intervention registry to arbitrary hard interventions: deleting incoming edges is a different source operation and must be checked separately against projection and selection compression. No equality of arbitrary full-law binary predicates is claimed, and the lower bound's oracle restriction remains essential. No finite-sample or minimal-faithfulness extension is proved. Runtime formal checking remains unperformed.

## Sources

Hou, Xiaotian; Park, Kwangmoon; Li, Hongzhe. Statistical Inference for Causal Discovery under Selection and Latent Variables via Single-Target Interventions. arXiv:2609.28856v1, 2026. Selected SIS assumptions, MAG marks, separate-indicator equivalence and original target.
https://arxiv.org/html/2609.28856v1

Richardson, Thomas S.; Evans, Robin J.; Robins, James M.; Shpitser, Ilya. Nested Markov Properties for Acyclic Directed Mixed Graphs. Annals of Statistics 51(1), 334–361, 2023. Proposition 1 and Supplement A.3–A.4; ordinary latent-projection separation only.
https://arxiv.org/pdf/1701.06686v6

Richardson, Thomas S.; Spirtes, Peter. Ancestral Graph Markov Models. Annals of Statistics 30(4), 962–1030, 2002. Selected maximal ancestral projection and endpoint semantics.
https://www.cmu.edu/dietrich/philosophy/docs/spirtes/annals2002.pdf

Sadeghi, Kayvan. Stable Mixed Graphs. Bernoulli 19(5B), 2330–2358, 2013. Prior marginalization/conditioning representations, closure and DAG realization results.
https://arxiv.org/pdf/1110.4168

Meek, Christopher. Strong Completeness and Faithfulness in Bayesian Networks. UAI 1995, 411–418. Discrete faithfulness and nonzero-polynomial arguments, extended here explicitly to a fixed selected slice by state relabeling.
https://arxiv.org/pdf/1302.4973

Kocaoglu, Murat; Jaber, Amin; Shanmugam, Karthikeyan; Bareinboim, Elias. Characterization and Learning of Causal Graphs with Latent Variables from Soft Interventions. NeurIPS 2019.
https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf

Zhou, Zihan; Kocaoglu, Murat. Towards Completeness in Causal Discovery from Soft Interventions with Known Targets. ICML 2026. Primary pp. 4–7, Appendix B.1–B.5, algorithms and complexity appendix inspected directly. Prior no-selection common-source realizability and completion; not assumed as a selected-case lemma.
https://proceedings.mlr.press/v306/zhou26s.html
https://raw.githubusercontent.com/mlresearch/v306/main/assets/zhou26s/zhou26s.pdf

[Query certificate](LATENT-SELECTION-IMEC-CERTIFICATE.md)
[No-selection special case](NO-SELECTION-FINITE-REALIZATION.md)
[Elementary-query lower barrier](RESTRICTED-INTERVENTION-BARRIER.md)
