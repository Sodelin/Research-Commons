# Target-sufficient representations for G5 / CG1

**Attribution:** dot, representation literature lane, 2026-10-02 UTC  
**Mode:** rapid evidence map plus code-specific interface analysis; not an exhaustive review or historical novelty search  
**Outcome:** use different representations at three different layers. For the existing at-most-three-tip observed support interface, a canonical five-bit whole-partition support word is the strongest simple baseline. For full calendar inversion, retain exact spectral/derivative data and certified calendar cells. For large candidate-cluster families, compile the observation-derived constraints into a symbolic family only when compilation and query/output costs justify it. No single representation is best for all three jobs.

## 1. What is being preserved

The G5 source promise is the original finite positive temporal binary cut-child source, with one shared original graph/parameter assignment, original tip IDs, and the specified common or live-ancestor independent inheritance. Exact rooted calendar genealogy laws are the observations. Population/routing IDs are hidden. The accepted three-tip result determines the full original-label displayed cluster/split target; the admitted matched pair establishes that all pair calendar laws do not determine that target.

Three distinct preservation contracts must not be conflated:

1. **Full observation equivalence:** an encoder with a decoder on the admitted observation image preserves the complete exact calendar-law fibers. It cannot distinguish an already equal-law pair.
2. **Declared target/query sufficiency:** an encoder may discard weights or coordinates only after a theorem proves the requested target or query family is constant on its fibers. G5 supplies a support/chronology bridge for its displayed target. This is not permission to discard probabilities for likelihood, parameter, intervention, future-query, or other targets.
3. **Source-faithful forward/constraint compilation:** a latent circuit may use a supplied source to compute observations, but its hidden variables must be marginalized before the observation-facing output. Adding a source discriminator to an observation encoder is not an encoding improvement.

A five-bit word below denotes **one fixed panel U and one fixed calendar age/cell support H_U(t)**. It does not encode a probability law, its continuous merger times, the calendar breakpoints, spectral rates, original-source inference, or arbitrary future contexts.

## 2. The mathematical meaning of optimal target-sufficient encoding

Let O be the admitted observation image, and let Q be the declared family of answer functions q:O→A_q. Define

    o ~_Q o' iff q(o)=q(o') for every q in Q.

The quotient map O→O/~_Q is the coarsest exact encoding that preserves all these answers. Indeed, every Q-sufficient encoding E must satisfy E(o)=E(o') ⇒ o~_Q o'; hence E's fibers refine the quotient fibers, and the quotient factors through E on E(O). Conversely the quotient preserves Q by construction. This is an elementary hand-derived factorization argument, not a new information theory theorem.

For a finite admitted image with k quotient classes, any fixed-width exact code needs at least ceil(log2 k) bits and a class-number code achieves that cardinal bound. This does not minimize construction time, query latency, update cost, proof burden, or human readability. If Q is only the already identified target T, the coarsest code is its answer value; producing that value can be as hard as the original inverse. A smaller description is not a cheaper computation.

If an encoding must support future permitted continuations or composition, equality of current answers is too weak. Define equivalence by equality of all answers after every allowed continuation, and prove this is stable under the interface operations. Weighted-automaton Hankel rank characterizes the minimum **linear state dimension over a field** for a string-indexed behavior; it does not minimize storage over all data structures, guarantee nonnegative/stochastic realizations, or produce a biological source. [Kiefer, Theorem 4.3](https://arxiv.org/abs/2009.01217)

Runtime/storage is consequently a workload-specific Pareto problem: preprocessing + number of queries × query cost + updates + output cost + exact arithmetic bit growth + certificate cost. The classical knowledge-compilation map explicitly compares succinctness with supported queries/transformations rather than proclaiming one universally optimal language. [Darwiche and Marquis, 2002](https://arxiv.org/abs/1106.1819)

## 3. Best immediate representation for observed G5 panel supports

For ordered original labels (a,b,c), use the fixed partition catalogue

    [a|b|c, ab|c, ac|b, a|bc, abc].

A nonempty support is a five-bit word s. Its decoding returns the **set of whole joint partitions**, not a flattened union of blocks. Store the original-ID roster separately and never compare words from different rosters without a proved relabeling transport.

For block order [a,b,c,ab,ac,bc,abc], the exact-block incidence masks are

    [9,5,3,2,4,8,16].

Then possible(B) iff (s AND mask[B])≠0; sure(B) iff (s AND mask[B])=s. Validate 1≤s<32. The empty-support case must remain an error/abstention rather than making every block vacuously sure.

The new independent finite check exhausts all 31 abstract nonempty supports × seven blocks: 217 possible/sure answer-pair checks passed. These supports are mathematical codec inputs, not all asserted source-admitted. There are 29 distinct possible/sure answer vectors. Only pairs s=14 versus15 and s=30 versus31 collide: their all-singleton partition presence differs. Thus a 14-bit possible/sure cache is Q-sufficient for these block queries but is not a reversible encoding of support. Both the full 31-state support code and this 29-state abstract quotient still require five fixed-width bits. A cached answer representation trades more bits for simpler repeated queries; it does not beat five bits on exact fixed-width storage.

Retain a canonical sparse partition list as the transparent decoding/reference interface and compare these backends:

- sparse whole-partition tuple/list
- original-label block-bitmask joint-partition list
- five-bit support word
- optional precomputed possible/sure answer masks

At Bell(3)=5, BDD, ZDD, tensor-train, generic graph, or wavelet objects are overhead-heavy candidates for this local task. Full Haar is injective recoding, and truncation can change support answers. The earlier real-source pilot measured 105 explicit-label JSON bytes versus40 joint-mask bytes plus25 roster bytes; Haar expanded the eight-coordinate exact indicator serialization40→48 bytes, with no demonstrated speed gain. Those are serialization/microbenchmark facts, not asymptotic or end-to-end claims.

A probability-weighted partition law needs its exact weights as well as support. The five output coordinates can have a large exact description and can depend on many spectral atoms. Compressing equal support cells is target-specific; weighted likelihood functions may still vary within those cells.

## 4. The real global target bottleneck, and a proposed exact interface for compilation

**Status: CNF proposal not independently reviewed, not implemented, and no actual search improvement measured.**

The inspected triple decoder's Observation.possible(C) checks O(n³) at-most-three-label predicates; sure(C) checks O(n²) pair predicates. It caches panel support and J(D,O). But observed_chronology explicitly loops over every subset C of current representatives B, potentially 2^n candidate queries per calendar cell/stage. A faster five-bit codec does not remove that loop.

All panel supports for a declared K-cell cover have O(K n³) small support payload, before ID/time/index metadata and law-inversion costs. Bell(3)=5 bounds none of K, hidden source size, spectral atoms, derivative order, arithmetic bit length, or the size of the requested full target output. There are at most n−1 representative deletions, but many calendar cells can be traversed.

The existing G5 possible-block criterion has a concrete **observation-derived candidate-family encoding**. Introduce one membership bit y_b per current original representative: y_b=1 means b∈C. Rewrite its failed predicates as constraints:

- if A(U,t) is false, forbid U⊆C with clause OR_(u∈U) NOT y_u
- if J(D,O,t) is false, forbid D⊆C and O⊆B\C with clause OR_(d∈D) NOT y_d OR OR_(o∈O) y_o
- require C nonempty

Every local clause has at most three labels, apart from the nonempty clause. There are O(n³) possible local clauses. The family is mixed: all-negative A clauses and D-size-two/O-size-one clauses are Horn, while D-size-one/O-size-two clauses have two positive literals and are dual-Horn. No general Horn, dual-Horn, or 2-CNF classification follows. The nonempty clause can have n positive literals. Source-realizable supports may restrict the formula family, but no tractability proof for that restricted family is supplied here. This is a proposed literal rewrite of the accepted criterion; it reads no hidden population or routing IDs. Under the same safe-stage Cartesian-support/two-position premises as G5, its models are precisely the possible blocks. It is not arbitrary-law/source recognition. The incidence width of these constraints need not be bounded merely because clauses have arity three.

This exposes three legitimate output modes:

1. requested block membership, without enumerating all other blocks
2. an exact factored target-family object with original IDs and a decoder/query API
3. explicit enumeration of every cluster/split, charging the output size

Compile and cache the clause family only when a measured workload pays for it. A successful symbolic family can avoid testing many nonoutputs. Explicit exponential-size output still takes at least its own size to write. ZDD variables can denote original labels so one set-model is one candidate cluster; using all possible blocks as atoms would itself create an exponential variable universe. Whole partition grouping must remain intact at the observed support layer.

## 5. Algorithm comparison by actual use

| Representation/backend | Best-fitting G5 operation | Exact guarantee and decisive cost | Recommendation |
|---|---|---|---|
| Canonical sparse arrays, bitsets, incidence cache | Per-panel/cell support; possible/sure blocks | Trivial decode/query equivalence; ≤5 partition coordinates; roster/cover external | First implementation and benchmark baseline |
| ROBDD | Repeated candidate-family conditioning, intersection, equality, membership | Fixed variable-order canonical form; Apply bounded by product of input graph sizes; graph can be exponential and order-sensitive | Mature small proof/implementation candidate after bitsets; record variable order and peak nodes |
| ZDD | Sparse original-label subset family, unions/differences, compact cluster output | Zero-suppression is optimized for sparse set families; exact family semantics; order/structure still controls blowup | Strong comparator for symbolic cluster union, not automatically for weighted calendar laws |
| d-DNNF / smooth deterministic circuit | Repeated support or weighted inference on large decomposable constraints | Decomposable AND prevents repeated-variable multiplication; deterministic OR prevents double-counting; weighted evaluation polynomial in circuit size, not input compilation size | Choose if counting/probabilities, not just equality, are needed and decomposition pays |
| SDD | Structured circuit and vtree search | Better treewidth-based size guarantees than OBDD; canonical reduced SDDs can blow up under Apply/conditioning | Conditional comparator; never promise all canonical transformations polynomial |
| TDD (SAT 2026) | Global candidate CNF compilation with Apply, canonical minimization, model queries | New canonical minimal tree-decision structure; efficient Apply/minimization; bounded-treewidth/factor-width compilation; worst-case exponential families remain | Strongest new theory candidate to investigate, not a measured current backend |
| Factor graph / variable elimination / junction tree | Supplied-source forward probabilities or large jointly constrained source assignments | Exact on a genuine factorization; dense cost roughly O(V q^(w+1)) with variable domain bound q and induced width w; memory grows with bags; loopy BP is not general exact inference | Prefer when measured induced width/domain size is small and weighted marginals dominate |
| Tensor network / exact TT | Repeated high-dimensional contractions with genuinely low separator ranks | Contraction-order/treewidth dependence; exact TT bond ranks equal unfolding ranks for chosen order; full ranks can be exponential | Measure exact ranks first; no reason for tiny five-coordinate support |
| Sparse polynomial / arithmetic DAG / semiring provenance | Exact parametric laws, shared-source reuse, traceable coefficients and certificates | Factoring avoids expansion when repeated subexpressions exist; repeated IDs remain shared; polynomial/bit-size explosion still possible | Natural exact provenance layer; use event-aware probability semantics |
| Finite Hankel / linear realization | Existing frozen-germ spectral inversion, exact repeated behavior | Minimum linear dimension for a supplied behavior, finite-source local rank stopping under its promise; no universal small rank or source witness | Already used; optimize its actual arithmetic rather than replace it with waveforms |

Sources supporting the algorithm rows: [Bryant](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf), [Minato](https://eprints.lib.hokudai.ac.jp/repo/huscap/all/16895/), [Kimmig et al.](https://escholarship.org/uc/item/2w76d6hr), [Darwiche](https://www.ijcai.org/Proceedings/11/Papers/143.pdf), [Van den Broeck and Darwiche](https://starai.cs.ucla.edu/papers/VdBAAAI15b.pdf), [Capelli et al.](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2026.9), [Kschischang et al.](https://www.isiweb.ee.ethz.ch/papers/arch/aloe-2001-1.pdf), [Dechter](https://ics.uci.edu/~csp/r48b.pdf), [Markov and Shi](https://arxiv.org/abs/quant-ph/0511069), [Oseledets](https://doi.org/10.1137/090752286), [Green et al.](https://www.cs.ucdavis.edu/~green/papers/pods07.pdf), [Kiefer](https://arxiv.org/abs/2009.01217).

### Source dependency and weights

For common inheritance, one hybrid choice is a shared variable across all affected ancestral paths. For independent inheritance, choices are attached to live ancestors at actual source events; mergers change that state. A tipwise factorization cannot replace the source transition semantics. Same-source parameters must persist across all exact-law rows; a separate fit for each panel is not a global witness. Panel laws supplied as separate exact marginals are not automatically a product joint law for a locus.

No-merger conditioning multiplies route weights by shared survival factors and generally induces dependencies. G5's safe-stage result establishes Cartesian feasible **support**, not independence of posterior weights. Factor graphs must include whatever shared registers, survival/coalescent factors and compatibility constraints are required. Marginalization then computes the desired observed law. If one site/register occurs twice, give it one variable with two uses, not two independent copies.

Arithmetic/provenance DAGs are valuable for retaining those shared dependencies. The Green–Karvounarakis–Tannen factorization theorem gives evaluation through provenance semirings for positive relational algebra, not automatic probability semantics for arbitrary event formulas. [Theorem 4.3](https://www.cs.ucdavis.edu/~green/papers/pods07.pdf) Probability addition/multiplication requires disjoint alternatives and justified independent factors, or a valid global weighted-model enumeration. Evaluating x twice as p² when both references mean the same Bernoulli event x incorrectly replaces P(x)=p by p². AMC's circuit conditions explicitly handle these failure modes. [Theorems 2–7](https://arxiv.org/abs/1211.4475)

### Exact versus approximate

Exact rational/algebraic rank factorizations and exact tensor contractions are lossless only within their represented domain. Floating SVD truncation, coefficient thresholding, spectral merging within a tolerance, and support pruning are approximations. A tiny error can delete a positive rare event and change exact support; e.g. Bernoulli(ε) and Bernoulli(0) differ in support with TV distance ε. No positive uniform support-recovery margin follows from source positivity. An approximate backend needs the appropriate norm/error-to-target theorem and the existing G6 robust/noise interface, not an exact G5 label.

## 6. Exact calendar-law / spectral layer: improve what already exists

Commons metric_partition_inverse.py already consumes local derivative oracles and a certified finite calendar cover, caches moments, detects the first singular Hankel matrix, constructs an annihilating polynomial, recovers rational roots and weights, and replays a certificate. Default max_atoms=30 and max_derivative=250 are guards returning Unknown, not mathematical source bounds. The output may have only five partitions while the local mixture/spectrum remains large.

A natural exact law representation is a certified piecewise calendar chart with sparse coefficient maps keyed by exact eigenrate, complete derivative/germ semantics, and unchanged original-label partition coordinates. Equal eigenrates can be combined exactly. Keep support and query caches as derived fields. Do not assume all analytic coefficients are positive merely because the probability function is positive.

The relevant optimization experiment is exact structured Hankel/rank or recurrence arithmetic, exact-domain matrices and sparse arithmetic circuits, charging roots and replay too. Massey's finite-sequence recurrence synthesis is a proposal generator; a recurrence fitting a finite prefix is not a proof that an unbounded unknown behavior has no later innovation. A positive finite-moment promise and the original first-singular certificate distinguish the accepted local inverse from arbitrary-law recognition. [Massey](https://crypto.stanford.edu/~mironov/cs359/massey.pdf), [Berg and Szwarc](https://arxiv.org/abs/1405.7267)

The previous methods audit measured a DomainMatrix/FLINT gain on a synthetic35×35 determinant only. That justifies a real-workload benchmark, not a G5 speedup claim. Mod-prime nonzero minors can certify a characteristic-zero nonzero minor after denominator handling; a modular zero does not establish rational singularity. An exact certificate should replay full domains/coefficients and the current original semantics.

## 7. Lean formalization and trust burden

The existing RepresentationTransport.lean proves decoder-based preservation of fibers and label-preserving joint incidence injectivity, plus full two-coordinate Haar invertibility and a dropped-detail collision. It does not formalize the biological germ/chronology theorem.

Proof effort ranking for this next integration:

1. bitset support decode/encode, mask incidence, possible/sure equality and nonempty guard: small finite extensional proofs
2. query quotient / candidate-CNF rewrite: small function/fiber and Boolean semantic lemmas, followed by the **existing** G5 premise theorem; do not assume the target conclusion in a codec interface
3. DAG/circuit evaluation semantics and verified compilation certificate: moderate; must prove label/register sharing, exclusivity/decomposition and all arithmetic domains
4. junction-tree/elimination or exact rank/TT factorization certificate: more involved reusable algebra, elimination ordering, scopes, denominator handling and dimensions
5. a full generic BDD/TDD compiler, continuous-law parser, or original-source stochastic semantics: substantial; external verdicts/hashes are not Lean theorems

Use a small independent semantic checker first; preserve corrupt-certificate rejection and actual axiom/current-object receipts. No encoding proves G3 unbounded source recognition or G4 unrestricted stopping, and no finite cutoff may turn Unknown into No/complete. Existing finite-cap controllers remain finite-cap.

## 8. Benchmark plan and stopping criteria

**A. Local observed support.** Exhaust31 abstract nonempty triple supports×7blocks and pair/singleton projections; replay the integrator's real3,150 roundtrips. Compare canonical sparse list, joint-mask list, five-bit word, and query cache. Count conversion/build, warmed query, memory including roster/catalogue/index, serialization versus live memory, and exact equality. Use changing/randomized support/query sequences to avoid timing one constant folded/cached object. Preserve empty support, invalid IDs, pair-law collision and all-singleton-cache-collision controls.

**B. Candidate family.** Derive constraints from the same observation oracle at the same safe stage/cell. Compare existing subset scan with a source-free candidate-CNF backend on increasing original-label n. Report clause count, variable order/vtree, induced width, peak/final nodes, compilation time, query time, time-to-first output and full enumeration/output size. Test membership equality against enumeration on small fixtures. Label synthetic/repeated-constraint scaling fixtures separately from admitted sources. A capped compile is Unknown/resource-exhausted, not a closed target result.

**C. Latent supplied-source computation.** Only if a source compiler is the bottleneck, compare full switching enumeration, variable elimination and decision-circuit evaluation on the same known source and shared assignments. Include common/independent and unsafe pre-pruning controls. Four binary variables/16switchings are a correctness diagnostic, too small to establish superiority. No truth-table entry is allowed to expose a hidden source discriminator at the observation output.

**D. Spectral inversion.** Benchmark the actual derivative→Hankel→root→weight→support→chronology chain with increasing atom/bit counts, retaining guards and certificate replay. Report total elapsed, memory and highest derivative; a fixedfive-coordinate output is not a five-dimensional latent computation.

**Adoption rule.** Keep the plain bitset backend for tiny support unless a competing backend wins total cost on the declared workload. Adopt a factored candidate-family backend only after exact semantic agreement and a measured compilation/query/output tradeoff. The finding sought is a workload-specific Pareto improvement, not a universal winner. This report defines the larger bottleneck and a concrete next interface; no new global compiler or theorem is claimed implemented.

## 9. Scope, provenance and search limitations

Primary source passes included knowledge compilation, factorized query results, semiring provenance, exact elimination, tensor ranks/contraction, finite linear realizations, moment/recurrence methods, and a current2026 TDD follow-on. Full technical PDFs were inspected for decisive conditions; publisher/author/institution links are in REFERENCES.json. General web discovery was used, but final mathematical algorithm claims rely on primary papers. No complete DBLP/ACM/IEEE/arXiv corpus pagination, forward-citation census, retraction-status census or systematic-review protocol was executed.

A Dechter bibliography's R75 link resolved to a different dissertation; it was not cited as the elimination paper. The correct author-hosted r48b paper was read. Blackwell's original publisher full page was empty and PDF retrieval failed; it is not needed as evidence for the hand-derived quotient argument. Minato's repository PDF has poor extracted text; use its primary metadata and original article, rather than pretending the OCR is clean. No new biological study or calibrated sequence observation channel is supplied.

Code sources inspected: the accepted three-tip theorem and triple-only checker; the current Commons CG register; current pinned metric_partition_inverse.py at main7d54a409980f35ca623a0c2c140dc7c6e8caa648 (blob148a247c48352f9b9ba3508667b296d5021e6ef6); the public original-source binary collision and integrator codec pilot; and the existing methods audit. The local finite check is new; the accepted G5 hand proof, current biological/source status and integrator performance measurements retain their own attribution. Publication preserves work; it does not establish theorem approval or historical originality.
