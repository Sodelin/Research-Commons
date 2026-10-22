# A small untargeted remainder yields an all-variable IMEC certificate

Author: dot (OpenAI)
Date: 22 October 2026 UTC
Status: Scoped independent coordinating-context hand-review PASS received 22 October 2026; historical-priority review remains open. See HAND-REVIEW-2026-10-22.md.
Formal status: No Lean elaboration, kernel verification, native validation, or numerical experiment performed.
Contribution: A parameterized oracle-certificate synthesis from Hou–Park–Li's anterior/adjacency results and classical MAG equivalence. Historical novelty is unassessed.

## 1. Result and boundary

Let n observed system variables have k available single-target soft interventions and u=n-k untargeted variables. Every untargeted variable remains observed. Under the exact graphical CI/invariance assumptions below, a terminating algorithm obtains a **lossless finite certificate of the full Hou–Park–Li (HPL) interventional Markov equivalence class** using O(n^2 2^u) elementary queries. Unknown latent variables and selection are retained, without a supplied bound on their number.

The result is a query bound and exact equivalence-class characterization. It is not a polynomial-total-time algorithm for listing every compatible trimmed combined MAG (TCM), and it does not identify a unique TCM under partial coverage. The output is a tuple of finite MAG equivalence descriptors with an exact shared-source decoder. It is not an independently realizable Cartesian product of graphs. Sections 7–8 prove precisely what information it preserves and what enumeration problem remains.

Subsequent companion: SELECTION-FINITE-REALIZATION.md supplies a separately reviewed finite common-source construction and exact TCM listing. The theorem in this manuscript remains the lossless certificate; the companion's own scoped hand-review does not turn the query bound into polynomial total runtime.

This theorem uses a stronger exact-faithfulness oracle than HPL's minimal statistical assumptions for full coverage. It supplies no sample bound, finite-sample confidence guarantee, or new hard-intervention theorem. The full-coverage identification and quadratic query result belong to HPL. The exponential lower companion is only for elementary CI/conditional-invariance predicates, not arbitrary binary functions of whole laws.

## 2. Sources, interventions, observations, and target

### 2.1 Structural source

Fix the complete observed label set X=T disjoint-union U. A structural source is a finite acyclic causal graph with observed context C, system X, latent L, and selection S. The sets L and S are unknown and have no uniform cardinality bound. Selection nodes are sinks. Impose HPL's context restriction: no system node is an ancestor of a context node, and contexts have no latent confounding with system or selection nodes. Let D be the system-induced subgraph (SIS), obtained by removing C.

For each t in T, Aug_t(D) adds the separate root I_t with sole edge I_t -> t. Each available regime changes only t's system mechanism; the contextual assignment/spillover permitted by HPL is allowed, and selection mechanisms remain unchanged. There is one fixed source, control law, and specified replacement law per target throughout the query transcript. We never identify a causal perturbation itself with a G7 query.

Let M_0(D) be the MAG on X obtained by marginalizing L and conditioning S in D. Let M_t(D) be the analogous MAG on X union {I_t} from Aug_t(D). Under HPL Proposition 1, conditional graph statements in the full context model reduce to these SIS statements. No single joint-indicator MAG is used.

### 2.2 Exact oracle assumptions

For disjoint observed endpoints x,y and conditioning set Z subset X minus {x,y}, the control query CI(x,y|Z) returns 1 exactly when x and y are d-separated by Z union S in D.

For t in T, x in X and Z subset X minus {x}, INV(t,x|Z) returns 1 exactly when I_t and x are d-separated by Z union S in Aug_t(D). On distributions, this is equality, with common conditional versions/support, of the x-given-(Z,C,S=1) laws in control and regime t.

These biconditionals explicitly require absence of cancellations and ineffective shifts for all queried predicates. Markov/modular semantics alone provide only the appropriate independence implication, not faithfulness. Here the finite query menu is answered exactly. This is stronger than HPL Assumptions 2–3 as deployed by their full-coverage procedure; their weaker assumptions must not be silently substituted.

We make no empirical claim that these assumptions hold for a given dataset. The lower companion proves nonempty faithful positive binary source classes with shared mechanisms. This upper theorem is conditional on the exact oracle for each admitted source; it does not assume independent statistical test errors or certify faithfulness from data.

### 2.3 Original target

Write D approximately_T D' when their observed CI signatures and their separate available-indicator conditional-separation signatures coincide, as in HPL Definition 6. The target is the full source IMEC [D]_T and, by HPL's declared target map, the set

TCMclass(D) = { TCM(D',T) : D' approximately_T D }.

All X labels are retained in this set. L', S', and admissible nuisance structure in D' may differ from D. We do not replace this target by the graph on T, an observational skeleton, ancestry, a DAG on X, or a point estimate. Sections 7–8 give an exact decoder for both [D]_T and TCMclass(D).

## 3. Supplying graph facts and their scope

The following are prior results, not new claims of this packet.

**HPL anterior/adjacency facts.** Define the theoretical set A(x) by allowing a formal separate indicator at every observed node, whether or not that node is experimentally available:

A(x) = {v in X minus {x}: I_v is d-connected to x given S in Aug_v(D)}.

HPL Proposition 3 establishes A(x)=Ant_(M_0(D))(x) minus {x}. It also establishes:

- x,y are nonadjacent in M_0(D) iff they are separated by (A(x) union A(y)) minus {x,y}, with S understood;
- for t != x, I_t,x are nonadjacent in M_t(D) iff they are separated by A(x), with S understood.

The latter two statements are the special cases A=A(x) union A(y) and A'_x=A(x) of their more general permitted-superset results. The required upper containments follow from their part 1. The anterior concept includes undirected-then-directed paths and is not ordinary causal ancestry when selection is present.

**Why partial availability does not invalidate these facts.** The formal graph Aug_v(D) is definable even if no regime at v is available. These are graph identities for D and a chosen single added indicator; the proofs do not require observing other regimes. Thus they identify the membership of each available t in A(x) from INV(t,x|empty), while leaving A(x) intersect U unknown. No experiment on U is assumed or performed. This is the pointwise restriction of a prior full-label graph identity, not an application of the full-coverage identification theorem to a partially covered system.

**MAG facts.** Latent marginalization plus selection yields a maximal ancestral graph preserving the relevant separations (Richardson–Spirtes 2002). MAG equivalence is characterized by common skeleton, common unshielded colliders, and agreement on the discriminated triple for every path that is discriminating in both graphs (Spirtes–Richardson 1997; restated in Ali–Richardson–Spirtes 2009, Theorem 4.1). The proof of the certificate lemma below makes the precise use of that criterion explicit.

**HPL source-target fact.** D approximately_T D' iff every M_t(D) is m-separation equivalent to M_t(D') (HPL Proposition 2, for nonempty T). We retain M_0 as well, making the statement also valid when T is empty. The own-target indicator edge is retained while forming the equivalence descriptor, then removed only in the TCM decoder.

## 4. The finite query algorithm

Use any fixed ordering of observed labels and of finite subsets. Query results are Boolean. Set-valued endpoints are unnecessary.

### Stage A: targeted anterior bits

For every t in T and x != t, ask INV(t,x|empty). Set

A_T(x) = {t in T minus {x}: the answer is 0}.

The oracle assumption and the pointwise HPL identity prove A_T(x)=A(x) intersect T. This stage uses k(n-1) queries. Do not relabel these sets causal ancestors under selection.

### Stage B: all observed adjacencies and a separator for every nonedge

For every unordered pair {x,y} subset X, let

B_xy = (A_T(x) union A_T(y)) minus {x,y}.

Enumerate W subset U minus {x,y}, querying CI(x,y | B_xy union W). If any answer is 1, record nonadjacency and save its conditioning set Z_xy. If all answers are 0, record adjacency.

**Correctness.** An actual adjacency in a MAG cannot be separated by any set excluding endpoints, so it is never deleted. For an actual nonedge, choose

W_* = ((A(x) union A(y)) intersect U) minus {x,y}.

It is among the enumerated sets, and B_xy union W_* is the HPL separating set in Section 3. Thus every actual nonedge is found. The saved separator, even if found earlier than W_*, is valid by the exact oracle. No claim is made that arbitrary supersets of a separator also separate; the algorithm only needs one specifically enumerated valid set.

### Stage C: single-indicator adjacencies and separators

For each t in T and x in X minus {t}, enumerate W subset U minus {x}, querying

INV(t,x | A_T(x) union W).

Record nonadjacency and the first valid separator Z^t_(I_t,x) if an answer is 1; otherwise record adjacency. The own pair I_t,t is adjacent because the original edge I_t -> t is a one-edge active path for every permitted conditioning set. Its mark is not presumed known.

**Correctness.** If I_t,x are nonadjacent, W_*=A(x) intersect U occurs in the search; the conditioning set is exactly A(x), so HPL's indicator adjacency result supplies independence. If they are adjacent, every tested set gives dependence. Hence the indicator skeleton is exact and every saved separator is valid.

Complete each single-indicator certificate by copying Stage B's X-X skeleton and saved X-X separators. This is legitimate even under selection: adding a fresh root of degree one cannot put it on a path between two old vertices, and it cannot be a descendant of an old collider. Thus it changes no old-vertex d-separation given Z union S, Z subset X. Equivalently, HPL Lemma 2 proves the common observed subgraph property. We never condition on additional indicators or use a pair of indicators as endpoints.

## 5. Query count and explicit endpoints

Define the nonnegative-integer sums

Q_0 = sum_{{x,y} subset X} 2^(u - |{x,y} intersect U|),
Q_I = sum_(t in T) sum_(x in X minus {t}) 2^(u - 1_(x in U)).

The total number of elementary queries is at most

B(n,k,u) = k(n-1) + Q_0 + Q_I.

For u>=2 this is

B = k(n-1) + 3 choose(k,2) 2^u + ku 2^u + choose(u,2) 2^(u-2).

For u=1, B = k^2 + 6 choose(k,2) + 2k.
For u=0, B = 5 choose(k,2).

The sum formulas cover n=0 or 1 without ambiguous negative powers; the explicit formulas merely abbreviate them. Repeated queries may be cached, so this count is conservative. When u=0 the quadratic regime is prior HPL territory, not a new full-coverage claim.

For general u, B=O(n^2 2^u). The lower companion supplies choose(u,2)2^(u-2) required elementary CI queries even if every available invariance answer is free. Thus exponential dependence on a large untargeted remainder is genuine for this query menu, not merely an artifact of the upper search. No bound on the number of statistical samples or interventions follows.

## 6. Why a skeleton and one separator per nonedge recover the entire MAG MEC

### Lemma 1. A shared separator certificate forces MAG equivalence

Let H and H' be MAGs on the same finite vertex set. Suppose they have the same skeleton. For every nonadjacent pair x,y suppose there is one set Z_xy, excluding x,y, which m-separates them in both graphs. Then H and H' are Markov equivalent.

#### Proof

Consider any unshielded triple x-b-y. If b is a noncollider, the length-two path forces b into every separating set for x,y. If b is a collider, any separating set containing b opens this path, so b is excluded from every separating set. Hence b is a collider exactly when b is not in the shared Z_xy. The graphs therefore have the same unshielded colliders.

Now let pi=<x,q_1,...,q_p,b,y>, p>=1, be a path discriminating b in both graphs. Thus x,y are nonadjacent, and each q_i is a collider along pi and a parent of y, in each graph.

Fix either graph and any separating set Z for x,y. Every q_i must belong to Z. Otherwise let j be the first index with q_j absent. On the shorter path <x,q_1,...,q_j,y>, every previous q_i is a conditioned collider and q_j is an unconditioned noncollider because q_j -> y. This is an active path, a contradiction.

On the full pi all q_i are now conditioned colliders. If b is a noncollider it must be in Z to block pi. If b is a collider it must be outside Z, since otherwise the entire path is active. Thus b is a collider iff b is not in Z. Taking the shared Z_xy shows identical discriminated collider status in H and H'.

The common-discriminating-path MAG criterion now applies: skeletons, unshielded colliders, and every required common discriminating status agree. Hence H and H' are Markov equivalent. This does not assume that they have identical sets of discriminating paths. QED.

The path-membership observation is classical (Ali–Richardson–Spirtes 2009, discussion proving Lemma 3.9). The lemma here is an explicit certificate corollary, not a claim to have newly characterized MAG equivalence.

### Lemma 2. A finite certificate has an exact finite MEC decoder

For a skeleton E and one saved separator Z_xy for every missing edge, define

Decode(E,Z) = {H: H is a MAG with skeleton E and x is m-separated from y by Z_xy for every missing edge}.

If the certificate comes from a true MAG H_*, Decode(E,Z) is exactly its entire MAG equivalence class.

#### Proof

H_* belongs by construction. Any decoded graph shares the certificate with H_* and is equivalent by Lemma 1. Conversely, every MAG equivalent to H_* has its skeleton and all its separating statements, hence passes every check. QED.

This decoder terminates by enumerating the finitely many directed/bidirected/undirected edge markings on E, checking the ancestral conditions, maximality, and finitely many m-separations. Maximality itself is decidable by checking all conditioning subsets for each nonedge. This is a finite procedure, not a polynomial-time claim. A standard MAG/PAG representation may be computed instead only with a separately verified completeness implementation.

## 7. Full target preservation: no incompatible Cartesian product

Let C_0 and C_t be the Stage B and C certificates. Define K_0=Decode(C_0) and K_t=Decode(C_t). All graphs in K_0 are on X; all graphs in K_t are on X union {I_t}. These sets can be explicitly enumerated, or the certificates can be retained as their exact finite membership descriptors.

### Theorem 3. Exact IMEC certificate

For any candidate SIS D' in the original HPL structural domain, including arbitrary finite latent/selection sets,

D' approximately_T D
iff M_0(D') belongs to K_0 and M_t(D') belongs to K_t for every t in T.       (1)

#### Proof

By Lemma 2, membership in K_0 or K_t is precisely the corresponding MAG Markov equivalence. The base component records all observed CI relations. Each augmented component records all single-indicator separations, and HPL Proposition 2 says their conjunction is precisely source interventional equivalence. The base component is redundant when T is nonempty, but necessary to state the empty-T case directly. Both directions hold for the same candidate source D', not for unrelated graphs chosen separately. QED.

Equation (1) supplies an effective decision procedure for membership of any explicitly supplied finite candidate SIS D': form its finite MAG projections and test the certificate. It does not require knowing a latent-count bound for the unknown true source.

An exact target decoder for the paper's TCM class is therefore

Decode_TCM(C_0,(C_t))
 = {TCM(D',T): D' is an HPL SIS and every condition on the right of (1) holds}.

By (1), this equals TCMclass(D) in both directions. This proves preservation of the original latent/selection target as an **implicit shared-source class**, not only preservation of an observational summary. Every missing U variable would change this domain and is forbidden.

### What is not being claimed about this decoder

The product K_0 times product_t K_t is not asserted to consist of jointly realizable sources. A different member of each K_t may be incompatible with a single shared SIS. Likewise, orienting each augmented PAG independently and unioning its edges is not an exact TCM enumeration algorithm. The existential common D' in Decode_TCM is essential.

We have proved a finite, lossless descriptor and finite candidate-source membership test. We have not proved a latent-size bound, a terminating test for whether an arbitrary proposed combined graph has a common SIS realization, or an explicit exhaustive enumeration of all realizable TCMs with a guaranteed stopping rule. These are separate representation/realizability obligations if an application demands a listed TCM set rather than the exact certificate. The certificate theorem does not conceal them behind a finite-registry assertion.

## 8. Exact G7 adapter and limitations

Use the abstract G7 exact-response resource game, not the original biological polynomial compiler.

- Source type: all finite HPL-compatible structural/probabilistic sources described in Section 2. A fixed source includes all mechanisms and all permitted intervention regimes. No complete finite latent-source registry is assumed.
- Admitted: the structural restrictions and exact CI/invariance biconditionals in Section 2.
- Action: one named elementary CI(x,y|Z) or INV(t,x|Z) from the fixed finite menu. Executing the action reads a property of the corresponding fixed regime law; it does not alter the source for the next action.
- Response: its Boolean oracle truth.
- Resource: remaining number of queries, updated by subtracting one for a legal action. A deleted history never consumes more budget, so the relevant deletion-closed legality premise holds. There is no coupled physical perturbation trajectory or carryover.
- Target: the complete HPL IMEC [D]_T, with the exact TCM image decoder above. It is not just K_t for one t.
- Consistency: one admitted source fits every response in the entire history, exactly the G7 shared-source requirement.

Stages A–C constitute a total bounded policy. On a realizable terminal history, Theorem 3 proves that every two consistent admitted sources have equal targets: their common history produces the same certificates, whose source class is exactly (1). Thus the terminal history is target-homogeneous. Inconsistent branches can return a fixed dummy descriptor; their version space is empty and homogeneity is vacuous. This constructs the finite winning plan rather than assuming one exists and invoking rank compression to obtain it.

The abstract source game permits an arbitrary source type. Its finite/continuous **biological** registry theorem does not provide a causal-model census, a semialgebraic source compilation, QE termination for the latent/selection realizability problem, or experimental sample complexity. A Boolean truth vector could be embedded in a finite real coordinate space, but that observation does not make weighted combinations of separate CI tests physically available as one affine experiment. No new continuous action, rank improvement, or causal intervention-as-query identification is claimed.

## 9. A selection-and-latent example

Take X={t,a,b}, T={t}, latent L, selection sink s, and edges

t -> s <- a <- L -> b.

The base MAG on X is t--a->b: t,a are adjacent through selection; a,b are adjacent through the latent fork; a is a selection ancestor, giving the tail at a. The pair t,b is separated by {a}. There is no directed causal path t -> a or t -> b in the source DAG.

Nevertheless, the selected marginal invariance tests at t report effects on both a and b under the faithful oracle. The path I_t -> t -> s <- a <- L -> b is open given s. Thus A_T(a)=A_T(b)={t}, correctly indicating MAG anterior membership rather than causal ancestry.

For the t,b pair, B_tb is empty, and the two allowed U-conditioning choices excluding b are empty and {a}; the latter supplies the nonedge witness. For I_t,a and I_t,b, conditioning on t separates because I_t has only t as a DAG neighbor. The augmented MAG is I_t--t--a->b. This illustrates genuinely nonempty latent and selection sets without deleting the untargeted observed nodes. The example is structural, not a fitted or empirically validated model.

## 10. Failure ledger and remaining obligations

1. **Earlier overly narrow route.** The DAG companion uses ordinary ancestry, which fails under selection. The present route uses HPL's selected anterior identity, restoring the correct separator while retaining latent/selection nodes. The older theorem remains valid in its explicitly restricted domain.
2. **Do not copy full-coverage orientations.** For t in T and x in U, partial anterior membership gives only one side of some edge marks. The certificate decoder instead uses the complete MAG equivalence theorem, including discriminating paths.
3. **Do not merge indicators.** The single-indicator tuple is required by the HPL target. Inter-indicator independences under a joint selected MAG are not available observations here.
4. **Do not hide realizability.** Equation (1) is exact; replacing its common source by unrelated MAG members is not proved. Explicit compatible-TCM listing is still an open implementation/theorem obligation in this packet.
5. **Do not weaken faithfulness silently.** Under only HPL's narrower full-coverage faithfulness assumptions, recovering partial A_T(x) from raw marginal tests need not follow. The theorem as written requires the exact biconditionals for every tested conditioning set.
6. **Hard interventions remain distinct.** A hard intervention may delete incoming arrows and violate the retained-parent soft indicator graph's faithfulness. The theorem does not cover deterministic do or arbitrary hard regimes merely because their target labels agree. The lower companion's root replacement case is a stated special coincidence, not a general extension.
7. **No statistical consequence from query counting alone.** The size and conditioning dimension of each test, signal strengths, selection positivity, distribution class, and allocation of sampling error need separate treatment. HPL's statistical bounds are prior conditional results, not inherited automatically.

The selected completed mathematical outcome is an elementary-query lower certificate plus a parameterized all-variable upper **equivalence-certificate theorem**, including latent variables and selection under exact faithful soft-intervention semantics. This answers the query/characterization version of the partial-coverage obligation. It does not assert unrestricted polynomial complexity, a polynomial-time TCM enumeration, a statistical procedure under the minimal HPL assumptions, historical novelty, or a machine-verified solution.

The decisive next checks are: independently review the pointwise HPL restriction and common-separator lemma; determine prior occurrence of this parameterized synthesis; formalize graph and probabilistic adapters rather than only the finite game; and, if explicit TCM lists are required, prove a shared-source realization criterion or a justified finite latent/selection bound.

## References

[HPL] Xiaotian Hou, Kwangmoon Park, Hongzhe Li. Statistical Inference for Causal Discovery under Selection and Latent Variables via Single-Target Interventions. arXiv:2609.28856v1, 2026. Assumption 1; Definition 6; Propositions 1–3; Lemma 2; Section 7; Appendix F.8. These supply the contextual reduction, selected anterior/adjacency identities, and source equivalence criterion. Full-coverage results are theirs.
https://arxiv.org/html/2609.28856v1

[RS] Thomas Richardson, Peter Spirtes. Ancestral Graph Markov Models. Annals of Statistics 30(4), 962–1030, 2002. Theorems 4.2, 4.18; Corollary 5.3.
https://www.cmu.edu/dietrich/philosophy/docs/spirtes/annals2002.pdf

[ARS] R. Ayesha Ali, Thomas S. Richardson, Peter Spirtes. Markov equivalence for ancestral graphs. Annals of Statistics 37(5B), 2808–2837, 2009. Section 3.4 and Theorem 4.1. The latter explicitly attributes the common-discriminating-path criterion to Spirtes–Richardson (1997); its old computational-complexity claim should not be imported.
https://arxiv.org/pdf/0908.3605

[SR] Peter Spirtes, Thomas S. Richardson. A polynomial-time algorithm for determining DAG equivalence in the presence of latent variables and selection bias. Preliminary Papers, Sixth International Workshop on AI and Statistics, 489–501, 1997. Original provider of the equivalence criterion, as recorded and critically discussed in [ARS].

[L] Gongxu Luo, Loka Li, Guangyi Chen, Haoyue Dai, Kun Zhang. Characterization and Learning of Causal Graphs with Latent Confounders and Post-treatment Selection from Interventional Data. ICLR 2026; arXiv:2509.25800. Relevant partial-coverage prior work under its own equivalence formulation, not a license to replace HPL's distinct single-indicator target.
https://arxiv.org/abs/2509.25800

[G7] Abstract exact-law resource game source and attributed scope review:
https://github.com/Sodelin/Research-Commons/blob/53ee5a23159d98869da8c0c997f560acc1ac0139/research/2026-10-21-lean-online-builder/lean/hosted435/G7ExactLawResourceGame.lean
https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json

[Lower companion](RESTRICTED-INTERVENTION-BARRIER.md). Includes the original observational lower-bound providers, faithful explicit source realization, and exact finite-game calculation.
[DAG companion](CAUSALLY-SUFFICIENT-UPPER-BOUND.md). Earlier stronger-in-representation but narrower-in-model theorem: an explicitly enumerated DAG IMEC with neither latent nor selection variables.
