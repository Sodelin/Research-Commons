# Resumed exact quartet recovery: matching adaptive bounds and smaller shadows

Session: QUERY-RESUMPTION-20260930-1144Z. Contributor/publisher: Codex root, with individually attributed delegated construction, adversary, prior and review contributions. Date: 2026-09-30 UTC.

Recovered source: Research Commons main 64080751ca56eb58efd250a403ed9f9ab97868c7, an immutable input snapshot, not a live roster. Target: [EXACT-QUERY-01](../../communications/2026-09-30-root-exact-query-master.md), optimal deterministic adaptive recovery of BOTH the complete displayed split union and any common circular order, without a supplied order, blobtree or network. Source: all finite binary semi-directed LSA-rootable, outer-labeled planar, galled networks, arbitrary admitted finite levels and blob counts. Oracle: complete distinct displayed quartet topology support.

**Current verdict: matching Theta(n log n) adaptive growth proved and independently internally reviewed under the registered exact-support model and inherited source premises. Exact finite minima include Q*(4)=1 and Q*(5)=5.** Fresh-main inspection found Astra's stronger insertion learner after this lane had constructed an O(n² log n) fallback. Independent structural, local, query-budget and execution reviews support the stronger result. [OPTIMAL-ADAPTIVE-INTEGRATION.md](OPTIMAL-ADAPTIVE-INTEGRATION.md) is the current decision brief. The exact integer optimum for every larger n, formal verification, biological observation and historical novelty remain separate obligations.

## 0. Decision brief

[GALLAI-ADAPTIVE-THEOREM.md](GALLAI-ADAPTIVE-THEOREM.md) supplies a deterministic adaptive common-order learner for ANY nonempty binary-tree family with a common circle. It replaces a false binary-reference-tree shortcut with a valid Gallai hierarchy of interval blocks. Weighted parity repairs reorganize blocks together, and an adjacency cache reuses measurements across candidates. Full split recovery then follows by the inherited sparse stage, or elementary quadratic dense boundary queries.

The Gallai method's frontier at its construction checkpoint was:

    Omega(n log n) <= Q*(n) <= O(n² log n).

That fallback did not match the lower bound. The subsequently received Astra insertion theorem DOES match it in asymptotic growth; see the integration and independent reviews. Fixed schedules still need Theta(n³) even to return ANY compatible circle. Adaptivity escapes that obstruction by changing which measurements are requested after observing answers.

The full source support table also has a minimum-size exact Theta(n log n)-bit shadow. [MINIMAL-PROJECTION.md](MINIMAL-PROJECTION.md) gives encoders/decoders, a quadratic circular-distance shadow and O(n) finite-field moment symbols. Representation and stronger aggregate measurements are different from legal quartet-point acquisition.

## 1. Why a minimum exists, and what has not been proved

For each fixed finite n, an exact deterministic optimum Q*(n) exists and is attained by some finite decision tree. There are finitely many quartet-support profiles. Querying the entire table provides a finite upper bound: anchored equations determine common orders, then the full table supplies boundary tests for every split. Achievable worst-case budgets form a nonempty set of nonnegative integers, so have a smallest member. This proves existence, not its value or an efficient construction.

A known lower bound is a floor and can be loose. Proving Q*(n)>=c n log n does not produce a C n log n algorithm. Asymptotic optimality needs a matching upper bound under the same source, oracle and output contract. General infima need not be attained, but the integer finite-query setting avoids that additional issue.

Nolan's shared-control idea has a concrete implementation here: one quartet constrains several comparisons; a component correction moves whole blocks. Dependence and symmetry permit this. Arbitrary scaling or complex packing alone provides no decoder or acquisition saving.

## 2. Boundary ledger

| Obligation | Established result | Remaining limitation |
|---|---|---|
| Exact labeled output storage | Theta(n log n) bits | Inherits linear source split count; acquisition separate |
| Fixed-schedule order recovery | Theta(n³) queries | Does not apply to adaptive schedules |
| Adaptive full recovery | Theta(n log n), Astra insertion learner plus sparse decoder | Internally reviewed hand proof; exact all-n constants and external/formal review separate |
| Exact finite minimum | Q*(4)=1; Q*(5)=5 on actual admitted fixtures | Exact Q*(n) for n>5 not derived |
| Adaptive common-order stage | O(n² log n) for any common-circle binary-tree family | Query bound; polynomial unoptimized computation |
| Splits with correct circle | Inherited sparse budget 2n-6+4k ceil(log₂(n-1)); alternatively quadratic dense queries | Preserve sparse attribution and source count |
| Literal pair-parity completion | Quadratic rank needed on trees | Method-specific barrier, not a universal lower bound |
| One-baseline hidden-set adversary | O(n+k) eligible fixed hidden subsets | Excludes one route; moving/many-round adversaries remain |
| Complete fixed-anchor data to full splits | Impossible on inherited admitted N1/N2 collision | Additional unrestricted queries required |

## 3. Adaptive proof and implementation

Root at a taxon r. Keijsper–Pendavingh's established signed comparison equations impose parity relations between pair variables of the other taxa. True common orders satisfy all observed equations.

First scan directed triangle cycles, querying only when a cycle remains feasible in the current affine space. Every such answer increases rank; subsequent restrictions cannot restore excluded cycles. At most binomial(n-1,2)-1 queries leave a space in which EVERY assignment is transitive.

Relative to one current order, component colors obey c(x,z) in {c(x,y),c(y,z)} for x<y<z. Classical Gallai substitution, refined into contiguous runs, gives interval-module children with at most two quotient colors. A minimum proper-interval-module cover dynamic program constructs this hierarchy in polynomial time. High-arity nodes are allowed; a containing binary tree is unnecessary.

Weight each original color by the sum of child counts at nodes where it acts. Total weight W<=4n-8. Flipping colors of total weight w introduces at most 2w new adjacent pairs. Merge measured parity components by weight, flipping the lighter side only when needed. Each original color's containing weight doubles whenever it is flipped, so total flipped weight is at most W ceil(log₂ W).

Certify each candidate using r, every adjacent taxon pair and every third taxon. A noninterval clade has an adjacent inside/outside boundary plus a later inside member, giving a queried rejecting quartet. Cache across repairs. Only O(n log n) different adjacent pairs occur; each requires at most n-3 queries. Thus order recovery costs O(n² log n).

[adaptive_recovery.py](adaptive_recovery.py) implements learn_order and recover_all. Input taxa are integers 0,...,n-1. Sorted quartet a<b<c<d uses mask bits 1,2,4 for ab|cd, ac|bd, ad|bc. Full output uses a circle plus supported nontrivial gap pairs; singleton splits are known. Explicit bipartition expansion has separate output cost.

The reference implementation has polynomial unoptimized computation, conservatively O(n⁵) for hierarchy construction, and O(n² log n) cached-word storage. Index words require O(log n) bits. It does not claim O(n² log n) running time. Reported full counts include repeated queries across order and sparse stages.

[GALLAI-AUDIT.md](GALLAI-AUDIT.md) independently reviews the decisive proof and code. [GALLAI-PRIOR.md](GALLAI-PRIOR.md) supplies primary-source citations and the novelty boundary. The earlier [order_recovery.py](order_recovery.py) remains a dense-anchor reference with cubic queries, O(n³ alpha(n)) processing and quadratic working memory.

## 4. Full split recovery and inherited source inputs

With a common circle, each possible nontrivial interval split has an exact adjacent-boundary quartet test. The dense stage adds at most n(n-3)/2 queries. Therefore the complete output has an O(n² log n) construction for ANY common-order binary-tree family, independent of a source split-count theorem.

The implementation composes with the unchanged attributed Astra sparse method in ../2026-09-30-astra-sparse-query/sparse_quartet.py. Its budget is at most 2n-6+4k ceil(log₂(n-1)). The conservative reviewed source count k<=13n-27 gives O(n log n) for that stage. Topology relabeling preserves bipartitions, rather than merely changing bit positions.

Occurrence/port admission and linear-count proofs are explicitly inherited from [SPLIT-COUNT.md](../2026-09-30-root-exact-query/SPLIT-COUNT.md). A newer sharper count is not needed for this result. Biological realization, finite-confidence absence, gene-tree probabilities and direction/parameter identification remain separate observation obligations.

## 5. Actual execution

Run python verify_adaptive_recovery.py in this directory, without -O. [adaptive-recovery-verification.json](adaptive-recovery-verification.json) records:

| Control | Actual result |
|---|---:|
| All nonempty binary-tree families on four/five taxa | 32,774; 303 correct recoveries and 32,471 correct no-circle rejections |
| Additional feasible-family anchor checks | 206 |
| Inherited admitted N1/N2 level-two fixtures | Both checked at all five anchors; exact splits recovered |
| Random common-circle tree-family scenarios | 94, with n from 6 through 64 |
| Generic containing-tree counterexample | Handled by a valid high-arity Gallai node |

Independent full-split truth comes from graph edge cuts. N1/N2 admission certificates are reused and labeled, rather than newly certified. Random families need not be displays of one admitted network; the order theorem applies more broadly. These controls are not universal proof substitutes, biological evidence or speed benchmarks.

The independent reviewer also executed [gallai_audit_controls.py](gallai_audit_controls.py): 116,183 canonical color partitions screened, with 163 entirely transitive cubes and 3,254 adjacency checks passing. This tests the hierarchy beyond source-friendly examples.

Dense reference, adversary, projection and boundary receipts are preserved alongside their notes. Conditional structural codecs are proved with inherited premises but unimplemented.

## 6. Lower bounds and reductions

[adaptive-adversary-nonadaptive-order.md](adaptive-adversary-nonadaptive-order.md) proves a fixed-schedule lower bound ceil(binomial(n,3)/4): three pendant-triple resolutions are indistinguishable unless that triple is covered, yet no circle works for all three. It also proves the adaptive order-only Omega(n log n) bound while accounting for shared output circles.

[adaptive-adversary-hidden-pair-barrier.md](adaptive-adversary-hidden-pair-barrier.md), independently reviewed in [BOUNDARY-REVIEW.md](BOUNDARY-REVIEW.md), bounds eligible fixed hidden sets around one circular baseline with k splits: n for singletons, n+18k for pairs, n+12k for triples, 3k for quartets and zero for larger sets. Thus the inherited k=O(n) excludes a naive quadratic one-baseline hiding construction. It does not exclude moving baselines or other many-round adversaries.

[MINIMAL-PROJECTION.md](MINIMAL-PROJECTION.md) proves that a full split union regenerates every quartet support answer and all common orders. A circle plus supported gaps achieves the matching Theta(n log n) storage scale. Unit circular split distances invert by adjacent four-point differences. Finite-field power sums recover the sparse gap IDs via Newton identities. These classical tools are specialized with explicit precision, decoder and access accounting.

Moment measurements aggregate many support bits and are stronger than one quartet call. A complex scalar can pack information while still requiring the same precision bits; packing alone cannot bypass indistinguishable transcripts. The inherited complete-anchor collision independently blocks full-split decoding from any projection of that table.

## 7. Corrections and next maximal attack

The initial claim that every all-transitive affine space embeds one binary reference tree was false. A generic four-order counterexample is preserved. The prior audit also found a seven-taxon common-tree-family partial-support counterexample after small positive screens. The Gallai proof avoids these premises and retains the corrections.

A monotone insertion invariant fails on inherited admitted N1: a compatible circle after deleting a taxon need not extend by inserting it into any gap. A valid faster strategy must reorganize existing taxa or establish a stronger invariant.

[MAXIMAL-ADAPTIVE-NEXT.md](MAXIMAL-ADAPTIVE-NEXT.md) proves literal pair-affine completion spends quadratic rank even on trees. This did not constrain the structurally different near-linear insertion learner. The separator candidate and its discovery gap are retained as this lane's historical next attack; fresh uptake of the reviewed peer theorem supersedes that acquisition gap. Current finite-constant, formal and biological obligations are in OPTIMAL-ADAPTIVE-INTEGRATION.md.

## 10. Continuity and attribution

The root packet, source audits and sparse peer method retain their ownership. Current-main exact-query continuation receipt ASTRA-EXACT-QUERY-20260930T1156Z and its full assignment were read during this resumption. A dated receipt does not establish live execution. This uniquely attributed packet provides concrete complementary work for uptake, without reassigning other lanes.

Publication uses fresh main as base and a non-force update. Historical conditional notes retain dates and supersession labels. No unseen peer receipt, external theorem acceptance or continuing background execution is implied.

## 11. Process integrity

The actual source, target, oracle and ownership records were recovered before allocation. Close primary prior was inspected before novelty claims. The all-size arguments received independent internal review and implementation controls against graph truth. Fresh-main inspection prevented reporting an obsolete frontier and redirected work toward the peer's decisive stronger result. Proofs, finite screens, reused admission certificates and unimplemented codecs are separated. Failed premises are preserved. Exact finite constants, formal/external review and biological dependencies are not replaced by asymptotic closure.

## 12. Inference robustness

Storage, query count, runtime, output expansion and precision are different costs. A small code or solution dimension does not establish cheap acquisition. An attained finite-n optimum need not equal a currently known lower bound. A method-specific quadratic barrier does not exclude near-linear structural learning. Successful finite screens did not protect the false containing-tree premise. If the source count failed, the general adaptive theorem and dense split composition would survive, while linear storage and sparse source specialization would need revision. Sampling in place of exact support requires its own probability/margin contract. No clinical review score or empirical meta-analysis statistic is attached to these mathematical proofs.
