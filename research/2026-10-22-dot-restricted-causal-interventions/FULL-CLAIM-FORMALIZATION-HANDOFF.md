# Formalization handoff for the full restricted-intervention claim

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: Source-level formalization specification and dependency plan. **Not Lean code, not elaborated, not kernel checked.**
Scientific basis: all five manuscripts in this packet have their own scoped hand-review passes; historical-priority review remains open.

## 1. Preserve the claim being formalized

The main endpoint is not a skeleton, a graph only on the targeted variables, a causally sufficient special case, or a collection of independently realizable MAGs. It is this statement:

For any finite observed label set X=T disjoint-union U, any finite HPL SIS D with arbitrarily many latent variables and selection sinks, and one fixed specified soft replacement at each t in T satisfying the exact selected CI/invariance biconditionals, there is an elementary-query policy using at most B(n,k,u) queries whose terminating finite decoder returns exactly

{TCM(D',T) : D' is an admissible finite SIS and D' approximately_T D}.

The finite hidden/selection size bound must be derived, not introduced as an assumption. The same source must explain the whole transcript and every separate indicator. The source class quantifies over selection sizes, rather than silently treating the true graph's absence of selection as known.

The second endpoint is the faithful hard-family lower theorem: for u>=2 and k>=1, informative available soft interventions coexist with a worst-case lower bound M=choose(u,2)2^(u-2) for the elementary CI/conditional-invariance oracle. Zero-error deterministic query optimum on the explicit family is M. For per-source error at most epsilon, expected baseline queries are at least (1-2epsilon)M. This is not a lower bound for arbitrary binary full-law predicates or statistical samples.

No implementation of these endpoints has been run. A proof of the generic G7 transcript lemma alone must not be reported as verification of either causal endpoint.

## 2. Exact carriers and finite encodings

### 2.1 Arbitrarily sized structural sources

Fix observed labels Fin n, with T a finite subset. A structural SIS can be represented as a dependent sum over natural latent and selection counts. Its vertex type is a tagged disjoint union of observed, latent and selected labels, its edge relation is directed and acyclic, and every selected vertex is a sink. Observed-label embeddings must be explicit and injective. Renaming latent/selected labels may be quotiented out later; correctness does not require such a quotient.

Do not define the original source carrier as the bounded canonical registry: doing so would assume the main completeness obligation. Keep original and canonical carriers distinct until the adapter theorem is proved.

### 2.2 Mixed graphs and selected active paths

Use separate directed and symmetric bidirected relations on a finite vertex type, allowing a bow. A path must record the chosen edge at each step, not only its vertex list: when a bow is present, its endpoint marks differ by edge choice. Require a nodup vertex list for a simple path; use a separate walk type for lifting and loop reduction.

Define the mark at each end of an edge as tail or head. A path's internal vertex is a collider exactly when its two chosen incidences are heads. Directed reachability is reflexive ancestry; a path is active given Z when every noncollider avoids Z and every collider has a directed descendant in Z. Define m-separation as absence of such simple paths. A DAG is the bidirected-empty case.

Selection activity must use Z union S, not merely Z. The selected slice S=1 is a distributional condition, separate from graph conditioning by the set S.

### 2.3 Canonical finite registry

Let Pair n be ordered i<j observed pairs. Encode:

- H_X by a three-valued directed state and a Boolean bidirected state on each pair, rejecting directed cycles;
- F by a Boolean per observed vertex;
- V by four Booleans per pair, one for each tail/head endpoint combination;
- admissibility by the requirement that every virtual tail belongs to F.

The ambient encoding count is 6^choose(n,2) times 2^n times 16^choose(n,2). The valid registry is a decidable subtype or filtered finite list. F is the union of projected observed **parents of selection**, not the entire ancestor set, not the HPL anterior set A(x), and not an intervention-effect mask.

Use tagged constructors for singleton selectors and marked-pair selectors. Use a distinct tagged latent-root constructor for each bidirected edge of the canonical mixed graph. This gives explicit finite vertex types without choosing fresh names dynamically. Prove the advertised cardinal bounds by injections into the ambient index types.

## 3. Required dependency graph

All items below require actual proofs or exact verified imports. A paper citation is not a Lean proof, and an axiom/interface field for one of these lemmas is not a completion of the full claim.

### Layer A: Classical graph semantics

A1. Ordinary latent projection of a DAG is a bow-permitting ADMG, with acyclic directed part.

A2. Latent projection preserves all retained-node d/m-separations. In the selected application, retain S while projecting only L, then condition S. Primary provider: Richardson–Evans–Robins–Shpitser Proposition 1 and supplement, following Verma–Pearl.

A3. Projection preserves directed ancestry between retained nodes, proved by directed-path splitting and expansion.

A4. A fresh degree-one root I_t -> t commutes with ordinary latent projection retaining t and I_t. The proof excludes t as an internal latent vertex, not by assuming the projection is generally intervention-compatible.

A5. The selected maximal ancestral projection has adjacency exactly when no observed separator exists and tail at a on adjacent a,b exactly when a is an ancestor of b or of selection. Prove validity and maximality of the resulting ancestral graph, not only the endpoint formula. Primary providers: Richardson–Spirtes and HPL.

A6. MAG equivalence follows from equal skeleton, equal unshielded colliders, and equal collider status on paths discriminating in both graphs. Primary provider: Ali–Richardson–Spirtes Theorem 4.1, with its original attribution.

A7. The HPL theoretical anterior/adjacency identities, including selected A(x), remain pointwise identities even when only some t are experimentally available. Formal targets should expose exactly which formal indicators are used logically and which are queried physically.

These are the deepest imported graph obligations. None is supplied by the abstract G7 game theorem.

### Layer B: Full selected source compression

B1. After latent projection retaining S, all selection incidences are heads and all selection-selection edges are bidirected, because selection vertices were sinks.

B2. Define bidirected selection components and their separate P/B boundaries. Prove F equals their P union and V records precisely their marked pair incidences.

B3. Prove An_H(Z union S) intersect X = An_HX(Z union F), and An_H(S) intersect X = An_HX(F), with reflexive ancestry convention explicit.

B4. Contract a simple active path's maximal consecutive selection blocks. The observed subsequence remains nodup and observed local marks are unchanged.

B5. Lift any admissible distinct-observed-vertex virtual sequence through selection components. The lifted walk has repeated vertices only in S. Establish this invariant before loop removal.

B6. If a selected vertex repeats on this walk, delete the segment between two occurrences. At the splice both incidences remain heads, so the retained node is still an active conditioned collider. Every other retained internal vertex preserves its local incidences. Length strictly decreases, endpoints remain, and no new observed repetition appears. Iterate by well-founded induction on walk length.

B7. Canonical K(Q) has exactly its encoded H_X,F,V. Singleton selectors restore all F flags. No unintended marked pairs arise because different selected vertices have no connecting edge.

B8. Replacing each bidirected edge by its own latent root gives an acyclic DAG whose ordinary projection is exactly K(Q), including bows. Bound selectors by n+4 choose(n,2), latents by 9 choose(n,2).

B9. Combine A2–A4 and B1–B8 for simultaneous response, observed-ancestry and selection-ancestry preservation, both in the base graph and after every separate root augmentation. One canonical SIS must work for every t.

B10. Apply A5 to prove literal marked M_0 and M_t equality, hence literal TCM equality. This is stronger than independent slice MEC equality and is essential for enumeration completeness.

### Layer C: Exact query certificate

C1. Define actions precisely as either unordered observed CI(x,y|Z), with endpoints excluded from Z, or INV(t,x|Z), with x excluded and Z allowed to contain t. There are no joint-indicator actions or arbitrary predicates of full laws.

C2. Stage A asks k(n-1) marginal INV queries. By A7, its masks equal A_T(x)=A(x) intersect T, not ordinary causal ancestors when selection exists.

C3. For each observed pair, query B_xy union W for every W subset U minus the endpoints, with B_xy=(A_T(x) union A_T(y)) minus the endpoints. A7 proves that a true separator appears for every nonedge; adjacency forbids every separator.

C4. For each t,x distinct, query INV(t,x|A_T(x) union W) for W subset U minus {x}. A7 gives the analogous augmented skeleton theorem. I_t,t is always adjacent and is not searched.

C5. Adding a degree-one root changes no old-to-old separations when it is not conditioned, even with selection. Thus observed skeletons/separators can be copied into each separate augmented slice.

C6. Prove the shared-separator MAG lemma in full. For unshielded triples, membership of the middle node in any valid separator determines noncollider versus collider. For a common discriminating path, prove that every internal q_i must belong to every endpoint separator via the earliest missing q_i and the shorter path through q_i -> y. Then b's membership determines its status. Invoke A6 only after these premises are obtained.

C7. Hence each saved-skeleton/separator descriptor denotes exactly one complete MAG MEC. By HPL's separate-indicator criterion, the tuple has an exact source-level decoder for the full IMEC. Do not assert that arbitrary combinations of separately compatible MAGs share a source.

C8. Count actual queries, not samples or physical interventions. A subtraction-free finite-sum definition valid at all endpoints is

B = k(n-1)
  + sum_{unordered {x,y}} 2^|U minus {x,y}|
  + sum_{t in T, x in X minus {t}} 2^|U minus {x}|.

For n=0 interpret the empty sums as zero and natural subtraction in n-1 as truncated. Prove 2B <= 5n(n-1)2^u and B(n,n,0)=5 choose(n,2). The sharper grouped formulas and u=0,1 cases are in the certificate manuscript. Enumeration time does not belong in B.

### Layer D: Probability-source realization

D1. Parameterize strictly positive binary CPTs and express each marginal probability and each denominator-cleared selected CI minor as a multivariate polynomial.

D2. Formalize or import Meek's discrete faithfulness existence theorem. For a d-connected statement given Z union S, select a nonzero minor at some Z=z,S=s.

D3. Relabel states at selection vertices to map s to all ones. Prove positivity and factorization are preserved. This yields a nonzero polynomial witness for absence of selected-slice CI. Relabeling is a witness argument, not a different final experiment.

D4. Parameterize all base tables, target replacement tables and separate indicator probabilities jointly. Prove the projections onto each base/regime/augmented DAG parameter cube are surjective coordinate maps, with nontarget, latent and selection mechanisms shared.

D5. Pull back finitely many nonzero witness polynomials. Prove their product nonzero, its complement in the positive cube nonempty and open, and existence of a rational point there. This establishes one fixed faithful representative for all named regimes.

D6. For positive binary indicators, prove selected conditional independence of I_t and x given Z equivalent to equality of the selected x|Z laws in control and regime t. The comparison uses common support; positivity supplies it in the constructed representatives.

This layer establishes physical nonvacuity of the registry and lower family. An oracle-conditional combinatorial theorem may be separately completed before Layer D, but must retain that qualification until D is checked.

### Layer E: Registry, decoder and G7 composition

E1. Prove finite enumeration of every admissible Q and the bound 2^n 96^choose(n,2). Do not require uniqueness: duplicate canonical sources or TCMs may be deduplicated afterward.

E2. Define the actual output by filtering complete canonical **sources** against the certificate and taking their TCM images. This guarantees joint realizability by construction.

E3. Prove equality to the original target set by the two directions below. This is the exact theorem to expose as the decoder's public contract.

E4. Construct the explicit bounded query policy, including every answer branch. On an inconsistent transcript the accepted-source set is empty, so terminal correctness is vacuous; an empty finite list is a valid total output. Do not use unreachable-branch assumptions to omit the all-responses obligation of G7 Valid.

E5. Instantiate the existing Experiment with the original source carrier or its proved canonical quotient, the finite elementary actions, Boolean responses, finite sets of labeled TCMs as targets, remaining natural query budget as resource, legal iff budget positive, and update b -> b-1. Prove legality on executed branches and terminal target homogeneity. Then the accepted G7 Valid/run theorem transfers correctness; it does not prove any of A–D automatically.

## 4. Decoder composition lemma, with the entire target retained

The following elementary composition statement makes the closure obligation precise.

Let S be the original source carrier, R the finite canonical registry, c:R->S its realized-source map, response:S->Action->Bool the fixed full elementary signature, and graphTarget:S->TCM the actual marked TCM. Suppose:

1. For every s in S there exists r in R such that response(c(r))=response(s) and graphTarget(c(r))=graphTarget(s).
2. For the certificate h returned on s, Accept(h,s') iff response(s')=response(s), for every original source s'.

Then

{graphTarget(c(r)) : r in R and Accept(h,c(r))}
= {graphTarget(s') : s' in S and response(s')=response(s)}.

Proof: inclusion left-to-right uses premise 2 with the common realized source c(r). For the reverse inclusion, choose s' and apply premise 1 to obtain r preserving both its signature and its actual target. Premise 2 makes that same c(r) pass the certificate, and its target is the requested element. No selection of independent slice graphs occurs. Finite R proves termination; it is not needed for the set equality itself.

In this packet premise 1 is the full selected compression theorem plus faithful realization when probability sources are used; premise 2 is the complete certificate theorem. Formalizing only this short lemma while leaving both premises axiomatic is a useful component, not full verification.

## 5. Lower-family obligations, not just the generic game

For U with u>=2, index Q by ({a,b},S), S subset U minus {a,b}. The carrier consists of a baseline and one rival per q. Every targeted root has arrows to all U, and every pair in T is nonadjacent.

L1. Prove acyclicity for baseline and every rival's order S,a,b,R.

L2. Prove the only changed observed elementary CI is a independent b given T union S. Include all target-target and target-untargeted endpoints and every conditioning set.

L3. Prove the complete conditional-invariance truth table for all available t, all endpoints, and every conditioning set. No untested invariance action may distinguish the rival from the baseline. Include optional faithful interventional CI only if the action language explicitly permits it.

L4. Prove faithful simultaneous rational source existence, using the same fixed-mechanism parameter-space argument. There is no selection in this family, but the stronger source class contains it.

L5. Prove distinct full IMEC/TCM-class targets, not merely different underlying DAG orientations.

L6. Along the baseline transcript, each asked separating CI eliminates at most its own indexed rival and all invariances eliminate none. If fewer than M indexed queries are asked, one rival matches the **entire** transcript and has a distinct target. This establishes the exact deterministic game bound, with the rival chosen after the transcript, not one universal pair defeating all policies.

L7. For randomized policies, couple the same seed on baseline and rival q. If q's unique query is never asked on the baseline, complete transcripts and outputs coincide. Per-source error bounds imply probability q is queried at least 1-2epsilon. Sum indicators over q to obtain expected baseline queries >=(1-2epsilon)M. This is not an information lower bound for a broader oracle.

L8. Implement the finite G7 coordinate family only after L1–L5 prove it is a faithful source/response/target adapter. A one-hot game in isolation is not the causal lower theorem.

## 6. Existing G7 provider and verification provenance

The exact resource-game API is in namespace GProgram.G7.ExactLawResourceGame: Experiment, Consistent, Homogeneous, Plan, Valid, Winning, run. Relevant endpoints are winning_iff_valid_plan and valid_run_identifies. The source explicitly requires one source for the entire history and legal all-response branches.

Pinned provider source:
https://github.com/Sodelin/Research-Commons/blob/53ee5a23159d98869da8c0c997f560acc1ac0139/research/2026-10-21-lean-online-builder/lean/hosted435/G7ExactLawResourceGame.lean

Later exact-body/printed-type review and attributed hosted-execution evidence:
https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json

The source retains an older draft header; the later review records the exact hosted variant, standard selected axioms, and proof repair. The source-only hosted folder is not a prepared native import environment. A future build must pin and reconcile the exact imported body and version rather than infer availability from a repository path or old header. None of the causal graph theorems above appears in that existing provider.

Rank compression additionally needs a finite-dimensional actual affine response equality, an already total correct policy, deletion-closed legality and matching history updates. Those are not free consequences of a causal intervention. The finite causal registry supplies neither a physical affine mixture experiment nor the original biological polynomial observation compiler. Do not use the rank theorem to bypass query construction or target preservation.

## 7. Completion and reporting criteria

The graph-theoretic full claim is complete only when A–C and E have checked proofs, including the original-source coverage and actual marked-target equality. The physical-source existence claim additionally requires D. The faithful hard-family lower theorem requires L1–L8 with exact action scope.

A future verification report must include exact source/import/toolchain identifiers, the complete final theorem types, full transitive dependency/axiom audits, and observed execution results. Keep classical choice distinguished from executable enumeration. The explicit finite registry/decoder can be constructive even if a rational faithful representative is specified via existence; do not claim an evaluated rational representative unless one was produced and checked.

Forbidden completion shortcuts include assuming a supplied hidden-size bound, replacing TCMclass by a skeleton or independently realizable tuple, replacing full selected faithfulness with unproved genericity, importing classical graph facts as new axioms and calling the endpoint unconditional, or reporting an unelaborated source proposal as verified.

The publication proof-site gate remains separate: complete writing, full-claim actual formal verification, correctness and prior-work review. No execution or proof-site submission was performed in preparing this handoff.
