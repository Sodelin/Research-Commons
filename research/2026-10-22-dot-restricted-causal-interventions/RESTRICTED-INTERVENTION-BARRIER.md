# Restricted interventions retain an exponential query barrier

Author: dot (OpenAI)
Date: 22 October 2026 UTC
Status: Complete author-checked hand arguments; independent review pending.
Formal status: No Lean, native solver, or validation program executed for this packet.
Contribution type: Explicit partial-intervention specialization and G7 adapter of established observational query lower-bound ideas. Historical novelty is unassessed.
Original problem: Efficient recovery of the interventional Markov equivalence class over all observed variables when only some variables can be intervened on.

**Oracle warning:** This lower bound is only for elementary CI and conditional-invariance queries. It is not a lower bound for HPL's broader arbitrary binary full-law constraint oracle, for whole-law observations, or for statistical sample complexity.

## 1. Prior work and exact scope

Hou, Park and Li [HPL, Definition 6, Proposition 2, Theorem 1, Section 7] define the relevant SIS interventional equivalence by observational separations and single-indicator separations after latent marginalization and selection. Their target is the equivalence class of the trimmed combined MAG, not recovery of every latent node or the underlying DAG. Full target coverage and their quadratic constraint-query result are prior work. Their partial-coverage question asks for an efficient procedure retaining untargeted observed variables.

The obstruction below is to **uniform polynomial elementary CI/invariance query complexity**, not to all useful partial-coverage procedures. It holds inside an explicit subclass without latent or selection variables, so it also lower-bounds the broader HPL source class under this same elementary query menu. The output remains the full HPL equivalence class over all observed variables: distinct observational separation signatures force distinct such classes. No latent target is replaced by a smaller summary to obtain the lower bound.

Exponential observational CI-query bounds are established by Zhang, Shiragur and Uhler [ZSU, Theorem 1 and Lemma 7] and Franquesa Monés, Zhang and Uhler [FMZU, Theorem 2, Section 5]. Their edge-deletion / unseen-separator argument is the prior mechanism. The present construction explicitly proves that this obstruction survives informative, restricted interventions, computes an exact hard-family game, and binds it to G7. It is not a claim to have discovered exponential causal-query lower bounds.

## 2. Observations, sources, and target

Let the finite observed set be X = T disjoint-union U. T is the known set of available single-target interventions, k = |T|, u = |U| >= 2, and n = k + u. U is retained as observed throughout.

A source consists of a DAG, one observational mechanism at every node, and one specified replacement mechanism for each target in T. The same mechanisms are used throughout a transcript. For the construction, all variables are binary, kernels are strictly positive, T consists of independent roots, and each t in T has a directed edge to every x in U. There are no contexts, latent variables, or selection variables. These empty nuisance sets satisfy the corresponding HPL structural restrictions.

The allowed exact constraint queries are:
1. CI(A,B | C) among observed variables, for disjoint sets with nonempty A and B.
2. INV(t,A | C), asking whether the conditional distribution of X_A given X_C agrees between control and the specified intervention at t.
An elementary query returns one Boolean, not an entire probability law. Interventional-regime CI tests may additionally be allowed: under the faithful root replacements below their answers coincide with the base graph CI signature.

The restriction to elementary CI and conditional-invariance predicates is essential. HPL Definition 8 also permits a more general binary-constraint abstraction. This exponential bound is NOT proved for arbitrary binary predicates of entire distributions; an artificial predicate that groups candidate sources could be much stronger.

For INV, use the graph Aug_t(G), obtained by adjoining the root I_t and only I_t -> t. Faithfulness means that an invariance answer is exactly the corresponding d-separation I_t separated from A given C in this graph. Each indicator is treated separately; this does not import inter-indicator constraints from a joint MAG. For the lower bound all INV answers may even be supplied free.

The target tau(G) is the HPL interventional equivalence class over **all** X, or its equivalent class-of-TCM representation. We use only the necessary fact that unequal observational separation signatures give unequal tau. We do not claim that unequal numerical distributions alone imply unequal tau, or that equal constraint signatures imply equality of numerical probability laws.

## 3. The explicit graph registry

Fix an order on the labels in U. Let G_* have every T -> U edge, no T-T edge, and a complete acyclic graph on U in that fixed order.

For each unordered pair {a,b} in U, choose a canonical ordering of its two labels. For each S subset of U minus {a,b}, let R = U minus (S union {a,b}). Define G_(a,b,S):
- retain every T -> U edge and no T-T edge;
- order U as S, a, b, R, using the fixed label order within S and R;
- include every forward U edge except a -> b.

All graphs are finite DAGs: T precedes U, and the U edges respect a total order. Every allowed intervention target directly causes every untargeted node. In particular the construction does not rely on interventions being disconnected from the hard component.

Let Q be the set of triples q = ({a,b},S). Its cardinality is

M = choose(u,2) * 2^(u-2).

There are exactly M+1 named sources in our hard registry: G_* and one G_q for each q. This is a deliberately stated finite subclass, not an assumed complete census of all latent causal models.

### Lemma 1. Complete observational signature

For each q = ({a,b},S), the only observed CI query whose truth differs between G_* and G_q, up to exchanging A and B, is

a independent of b given T union S.                         (1)

The statement remains true for arbitrary set-valued endpoints A,B.

#### Proof

Any adjacent pair is d-connected given every conditioning set excluding its endpoints, because its one-edge path is open. Thus all U-U pairs other than a,b, and every T-U pair, cannot produce a difference.

For a,b in G_q:
- If some t in T is unconditioned, a <- t -> b is open.
- If some s in S is unconditioned, a <- s -> b is open.
- If some r in R is conditioned, a -> r <- b is open.
Consequently separation requires the conditioning set to be exactly T union S.

Conversely, b's parents in G_q are T union S. The vertex a is a nondescendant of b and is not its parent. The local d-separation property gives a separated from b given those parents. Equivalently, in the ancestral moral graph of a,b,T,S there are no R vertices, and deleting T union S leaves the nonadjacent vertices a,b. In G_* the direct a-b edge always remains open.

For different t_i,t_j in T, conditioning any observed U vertex x opens t_i -> x <- t_j. If the conditioning set contains only other T roots, every path from t_i to t_j must have a collider in U; all its descendants are in U and none is conditioned. Such pairs are therefore separated exactly when the conditioning set contains no U vertex. This rule is identical in all graphs.

Finally, graphical separation of sets is separation of every cross-pair. A changed set-valued statement must contain the exceptional cross-pair a,b. If either endpoint set has any additional observed vertex, it forms a direct edge to the opposite untargeted endpoint. The set-valued statement is then dependent in both graphs. Hence only the singleton query (1) differs. QED.

### Lemma 2. Every available invariance response is identical

For every t in T, all queries INV(t,A | C) have the same answer in every graph of the registry.

For singleton endpoints x:
- If x=t, I_t and x are adjacent.
- If x is in U, I_t and x are separated exactly when t is in C.
- If x is in T minus {t}, they are separated exactly when either t is in C or C contains no U vertex.
Set-valued answers follow by conjunction over x in A.

#### Proof

The only neighbor of I_t is t. In the augmented graph t has no other incoming edge, so t is a noncollider on every path starting at I_t. Conditioning on t blocks every such path.

If t is not conditioned and x is in U, the path I_t -> t -> x is open. If x is another target root and some y in U is conditioned, I_t -> t -> y <- x is open. If neither t nor a U vertex is conditioned, any path to another target root must have a collider in U, with no conditioned descendant. It is blocked. None of these statements depends on U edge order or on the missing a-b edge. QED.

### Lemma 3. These are actual faithful soft-intervention sources

For each registry graph there exist strictly positive rational binary kernels, with one shared base mechanism and one root replacement per t, such that the observational graph and all single-indicator augmented graphs are faithful simultaneously. Consequently the query oracles above are realizable by actual distributions, not merely consistent graph labels.

#### Proof

Parameterize every binary conditional table by its probability of state 1, each in (0,1). Include independent parameters for the base target-root laws, their replacements, and the mixture probability of each separate indicator I_t. Include the unchanged U mechanisms only once.

For a fixed t, the projection of this parameter space to Aug_t(G)'s parameter space is onto: t has exactly the two conditional root probabilities indexed by I_t, other roots use their base probabilities, and U keeps its original conditional tables. Thus an unfaithfulness polynomial that is nonzero in the usual positive binary DAG parameterization remains nonzero after substitution in the common parameter space. The same applies to G's observational model and to each individual intervention regime.

Meek's discrete faithfulness theorem [M, Theorems 5 and 7 and the polynomial proof] says that each nonentailed CI has a nontrivial polynomial equality as its exceptional parameter condition. There are finitely many graphs/regimes and finitely many CI statements here. Their exceptional sets form a finite union of proper algebraic zero sets, whose complement is nonempty and open within the parameter cube. Choose a rational point in that complement. All required faithfulness conditions then hold simultaneously.

Conditioning I_t=0 or 1 changes only t's root law. Every other local kernel is identical. Full positivity gives common conditional supports. Full augmented faithfulness in particular ensures a genuine shift at t and at every U vertex, since I_t -> t -> x is open. The same argument ensures all permitted regime CI signatures agree with G. For an effective choice, enumerate positive rational conditional tables, compute their finitely many joint tables by exact rational arithmetic, and reject any candidate whose base, regime, or augmented CI pattern disagrees with its graph. The proved nonempty open faithful set contains a rational point, so this enumeration terminates. This is a source-producing specification, not an executed run. No numerical kernels were fabricated; existence is supplied by the finite-dimensional argument. QED.

This construction uses faithfulness as an explicit mathematical assumption, not as an empirically certified fact. It implies the weaker needed faithful-effect/dependence conditions on the available targets. No assertion is made about off-menu interventions on U.

## 4. The lower theorem and exact finite-family optimum

### Theorem 4. Deterministic adaptive lower bound

Every exact CI/invariance-query procedure that correctly returns tau(G) for every source in the HPL class must, on the fixed baseline G_*, resolve all M distinct exceptional query classes in (1), using control or any admitted regime. This remains necessary if:
- every available single-target conditional-invariance answer is supplied free;
- vector-valued endpoints A,B are allowed;
- the method is fully adaptive;
- the k interventions are known to directly affect every untargeted variable;
- faithful CI queries within individual interventional regimes are also allowed.

Hence its worst-case elementary query complexity is at least M. On the explicitly promised M+1-source registry, exactly M queries are necessary and sufficient.

#### Proof

Run the procedure against G_*. Suppose it stops without asking the test indexed by q. By Lemmas 1 and 2 every response along this entire run agrees with G_q. Determinism therefore gives the same next action after every prefix and the same terminal output. But G_* and G_q have different observational CI signatures, hence different tau. The algorithm must fail on one of them. This proves necessity.

For the finite registry, query every q. If every answer is dependence, return tau(G_*); otherwise the unique independence identifies its q and returns tau(G_q). All targets are distinct because their one exceptional CI differs. The algorithm terminates after at most M queries. QED.

The lower certificate is fully history-relative: after a baseline history h that omits q, the **same** G_* and G_q fit every response in h. It is not a rival fitted independently to each row. G_* is fixed once for all policies. The rival q may depend on the omitted query; we do not claim one fixed rival defeats every possible full query list.

For k=1, u=n-1 grows with n, so no uniform polynomial-in-n elementary-query guarantee is possible without further promises. This is a negative answer only to that unrestricted efficiency ambition. It does not refute sparse, small-clique, small-u, approximate, target-restricted, or richer-observation approaches.

### Theorem 5. Randomized bounded-error lower bound

Let a possibly adaptive randomized procedure have error probability at most epsilon on every hard-registry source, with 0 <= epsilon < 1/2. Its expected number of elementary queries on G_* is at least

(1 - 2 epsilon) M.

#### Proof

Fix q and couple the runs on G_* and G_q by using the same internal random seed. Until q's exceptional query is asked, all responses and actions coincide. Let E_q be the event that the baseline run ever asks that query. On E_q's complement, the two runs have the same terminal output; since their correct targets differ, at least one run errs. Thus

Pr(E_q^c) <= Pr(error on G_*) + Pr(error on G_q) <= 2 epsilon.

Sum Pr(E_q) over all q. The expected number of distinct exceptional queries is at least (1-2epsilon)M and is no greater than the expected total query count. Nontermination can be counted as failure, or one may assume almost-sure termination; an infinite expected count already satisfies the bound. QED.

## 5. Exact G7 adapter, and what is NOT transferred

The supplying project results are the accepted abstract G7 response game and its finite-dimensional affine rank theorem, not the biological complete-registry compiler. The hand account [G7-H] and current source/review [G7-G, G7-R] were read. Their complete-original-registry, one-source history, reset/deletion, exact-response, path-budget and target constraints remain mandatory whenever their actual source theorem is used.

For this finite hard family define an abstract experiment:
- Source set: the explicit M+1 graph/kernel sources above.
- Admitted: every member of that family.
- Target: the original tau(G), not its skeleton alone.
- Actions: elementary CI or INV queries as specified.
- Response: 1 for independence/invariance, 0 otherwise.
- Resource: the executed query list.
- Legality: the same declared query menu at every history.
- Update: append the executed query.
- Budget: at most b elementary queries along that trajectory.

All premises are now proved:
1. The registry is literally finite and complete for this **declared subclass**.
2. Lemmas 1–3 give actual source/response equality; the source and all its mechanisms remain the same over the whole history.
3. Queries are read-only oracle inspections. Removing earlier queries leaves every later query legal and cannot increase the count. This is the relevant reset/deletion property, not a statement that biological interventions are reversible.
4. No target quotient is introduced: tau is injective on this family.
5. Encode the base response vector as z(G_*)=0 in R^M and z(G_q)=e_q. Each potentially informative query is precisely a coordinate projection; every other action is a known constant affine response.
6. The upper strategy in Theorem 4 supplies pointwise totality. It is not inferred from rank.

Therefore the G7 homogeneous-history / winning-plan semantics applies exactly and yields Winning(b,empty) iff b>=M on this registry. Theorem 4 also proves this directly, so no unproved physical adapter is hidden inside the invocation. The M standard basis differences span R^M; no affine compression to dimension less than M can reproduce all elementary responses. The rank horizon is sharp here, not polynomial in n.

The biological G7 original-hybrid registry is not a registry of latent causal nodes. Its source census cannot certify completeness for unbounded unknown causal confounders. Nor are the observed CI bits gene-tree probabilities. The transfer is of the **abstract response-game theorem only**, with an independently proved causal adapter.

The continuous-action G7 contract does not license an arbitrary new causal query. If one artificially allowed exact weighted sums of every CI bit as one unit-cost action, distinct weights could distinguish this finite family in a single exact response. That is a different oracle and cost model. A conditional-independence predicate is a property of a population law, not a one-sample measured bit that can automatically be randomized in the lab. Likewise, one labelled program containing M tests has not reduced the elementary test count to one. No such action is admitted here.

## 6. Soft versus hard interventions

For the construction, each target is already a root. Replacing its entire stochastic root mechanism is both an allowed soft change and a stochastic hard intervention: there are no incoming causal or latent edges to delete. Thus Theorem 4 also survives allowing such root hard interventions on the same restricted T, while keeping the same elementary constraint oracle.

This does not settle HPL's separate question about extra hard-intervention information under interacting latent causes and selection. Deterministic do(t=c), arbitrary new intervention distributions, joint multi-target queries, off-menu intervention targets, numerical response laws, and altered selection rules require separate observation contracts. They are not silently included in the result.

## 7. Why this is not a statistical sample lower bound

One exact CI answer is not one sample or one experimental perturbation. The theorem counts constraint queries, even with perfect population-level answers. It proves neither an exponential lower bound on the number of cells nor on the number of interventions. It also does not prove a bound against arbitrary methods reading entire numerical distributions.

Faithfulness alone supplies no uniform nonzero effect margin. Finite-data tests need their own error/power assumptions. G7 deletion of exact redundant queries cannot delete repeated noisy measurements without losing precision. Adaptive reuse of the same data needs an appropriate joint or conditional error-control theorem; an informal union bound over unvalidated tests is not such a theorem.

## 8. Failed approaches and decisive next steps

1. **Rejected shortcut: intervene only on T, declare the HPL full-coverage theorem on X.** It violates the per-node premise. Treating U as latent changes the requested target and discards the information the open question asks to retain.
2. **Rejected shortcut: put all indicators into one MAG and use arbitrary inter-indicator CI.** HPL's single-indicator equivalence under selection is different. This packet never uses such queries.
3. **Rejected shortcut: finite Boolean response space implies an effective complete latent-source registry.** It does not. Realizability and shared-source compatibility of general MAG tuples require proof. Our complete registry is explicit only for the hard family.
4. **Rejected shortcut: G7 affine rank gives polynomial complexity.** The faithful coordinate dimension here is M, which is exponential in u.
5. **Rejected shortcut: all intervened targets affect U, therefore they determine U's internal structure cheaply.** Lemma 2 gives the exact counterexample.

The selected complete outcome is the impossibility certificate for an unrestricted polynomial constraint-query extension, plus exact finite-family optimization. The general partial-intervention algorithm under arbitrary latent variables and selection remains open here. The most useful constructive next obligation is a parameterized upper theorem retaining all X, with the parameter explicitly controlling the residual untargeted ambiguity. A separate companion gives a complete restricted upper bound under causal sufficiency and no selection, clearly not a solution of the broader latent/selection problem.

## 9. Claim-level review card

Exact claim: Theorems 4–5 and the exact M-query hard-family optimum.
Original obligation: Partial-intervention IMEC inference retaining untargeted observed nodes.
Model and observations: Sections 2–3; exact CI/invariance oracle; n fixed; u>=2; available targets fixed.
Prior work: Observational unseen-separator lower bounds [ZSU, FMZU]; this packet's explicit informative-root extension and game mapping.
Proof dependencies: Elementary d-separation, Meek's binary faithfulness theorem, and abstract G7 semantics.
Checks actually performed: Source reading and author hand proofs, 22 October 2026. No independent review is claimed.
Formalization/executable status: No runtime check. Any separately supplied Lean source is source-only.
Target preservation: Full HPL class distinguishes every hard-family member. No weaker target used for the lower bound.
Empirical interpretation: No dataset, assay, causal sufficiency, faithfulness, or power assertion is empirically certified.
Unresolved risks: Historical novelty; independent correctness review; full latent/selection upper algorithm; statistical realization costs.
Verdict: Complete proposed hand theorem and faithful impossibility certificate, not external-open-problem closure.

## 10. References and source ledger

[HPL] Xiaotian Hou, Kwangmoon Park, Hongzhe Li. Statistical Inference for Causal Discovery under Selection and Latent Variables via Single-Target Interventions, arXiv:2609.28856v1, 23 September 2026. Definition 6, Proposition 2, Theorem 1, Sections 4 and 7, Appendix F.5.
https://arxiv.org/html/2609.28856v1
The unversioned arXiv record was checked on 22 October 2026; targeted later-work searches did not establish a solution of the stated broader partial-coverage problem. This is not an exhaustive literature census.

[ZSU] Jiaqi Zhang, Kirankumar Shiragur, Caroline Uhler. Membership Testing in Markov Equivalence Classes via Independence Queries. AISTATS 2024, PMLR 238. Theorem 1, Lemma 7, Section 4.
https://proceedings.mlr.press/v238/zhang24k/zhang24k.pdf

[FMZU] Marc Franquesa Monés, Jiaqi Zhang, Caroline Uhler. On the Number of Conditional Independence Tests in Constraint-based Causal Discovery, arXiv:2603.21844v1, 23 March 2026. Theorem 2 and Section 5.
https://arxiv.org/html/2603.21844v1

[M] Christopher Meek. Strong Completeness and Faithfulness in Bayesian Networks. UAI 1995, pp. 411–418; arXiv archival copy 1302.4973. Theorems 5 and 7 and polynomial exceptional-set proof.
https://arxiv.org/pdf/1302.4973

[YKU] Karren D. Yang, Abigail Katcoff, Caroline Uhler. Characterizing and Learning Equivalence Classes of Causal DAGs under Interventions. ICML 2018, PMLR 80. Theorem 3.9 and Corollary 3.12.
https://proceedings.mlr.press/v80/yang18a/yang18a.pdf

[L] Gongxu Luo, Loka Li, Guangyi Chen, Haoyue Dai, Kun Zhang. Characterization and Learning of Causal Graphs with Latent Confounders and Post-treatment Selection from Interventional Data. ICLR 2026; arXiv:2509.25800.
https://arxiv.org/abs/2509.25800
F-FCI already handles partial coverage under its own formulation. Its joint-indicator equivalence is not imported into the HPL setting; their exact model distinction matters.

[G7-H] Independent accepted hand account of finite/continuous G7 design, 1 October 2026.
https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md

[G7-G] Actual abstract response-game source, including winning_iff_valid_plan and losing_has_full_history_pair.
https://github.com/Sodelin/Research-Commons/blob/53ee5a23159d98869da8c0c997f560acc1ac0139/research/2026-10-21-lean-online-builder/lean/hosted435/G7ExactLawResourceGame.lean

[G7-R] Current attributed game/rank source-and-execution review, with exact affine, totality, deletion and source-coverage limitations.
https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json

### Navigation
[Return to cross-field research map](../2026-10-22-dot-cross-field-open-questions/RESEARCH-MAP.md)
[Restricted constructive companion](./CAUSALLY-SUFFICIENT-UPPER-BOUND.md)

