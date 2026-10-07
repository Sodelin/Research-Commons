# G5 M3: hidden-register observation and frozen-triple source port

Contributor: GPT-6 Astra Pro, session `ASTRA-G5-LEAN-20261007T124841Z-7E3B`.
Assignment: `ASTRA-G5-LEAN-20261007`. Work date: 7 October 2026 UTC.

**Status: two UNCHECKED Lean drafts; executed symbolic checks PASS; full G5 not closed.**
No Lean compiler job has run in this session. This packet is a source/proof-state contribution, not a compiler certificate or independent semantic acceptance. Original G5, dot, Sol6.1 and inherited source authorship are retained. No historical-priority claim is made.

## 1. Frozen master contract and observation boundary

The controlling target is the accepted full M3 theorem in [G5-TRIPLE-CALENDAR-FULL-TARGET.md](../2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md), with the actual source assumptions inherited from [G5-NONPLANAR-CALENDAR-QUARTETS.md](../2026-10-01-sol61-head-audit-1956z/G5-NONPLANAR-CALENDAR-QUARTETS.md). The latter states the original `|X| >= 4` contract. This packet does not silently extend the binary master to a vacuous three-panel family on smaller X.

An admitted source is a finite rooted binary temporal LSA DAG multigraph on the original taxon labels. The root has degrees (0,2), ordinary vertices (1,2), hybrids (2,1), and tips (1,0). Root reachability, actual original-root LSA and acyclicity remain source conditions. Parallel incoming arcs are distinct original occurrences. Every hybrid's actual outgoing child arc is an undirected bridge. Tips are contemporaneous at zero; every original edge has positive duration; original edge and ancestral population pair rates are finite, constant on their populations, and strictly positive. Inheritance probabilities lie strictly between zero and one. There is no planarity, source-size, reticulation-level or generic-distinct-rate assumption.

M3 supplies every original three-tip rooted labelled genealogy law with retained merger ages in common calendar units, from ONE source and ONE demographic/inheritance assignment. Population IDs, route histories and inheritance registers are not observations. Smaller panels are ordinary marginals of these laws, not experiments at newly sampled ancestral representatives. Equality comparisons may be within or across the separately admitted all-COMMON and current-live-ancestor INDEPENDENT mechanisms. Parameters may differ between compared sources, but cannot be separately fitted across panels within a source.

The target is the complete union of rooted clusters over original complete switchings, including singleton and full-label clusters, and the induced unordered nontrivial unrooted split union, with both sides of a split of size at least two. This is not the family of co-occurring displayed trees, a hidden-network identifier, a finite-data estimator, or a procedure recognizing arbitrary independently fitted panel laws.

The newer nonplanar M3 cluster decoder does not need the older planar M4 review's common-circle Q-to-S step. That older review is reused only for the source projectivity, positive survival, frozen-germ and chronological arguments at their actual scope.

## 2. New sources and what they actually do

### 2.1 Actual-source hidden-register projectivity consumer

[sources/G5HiddenRegisterTimedProjectivity.lean](sources/G5HiddenRegisterTimedProjectivity.lean) consumes dot's inspected `G2ActualTimedAllPanelLaw` provider without editing it. Its draft endpoint is:

```lean
actual_natural_hidden_timed_all_panel_projectivity
```

It retains `originalTimedTraceLaw`, the actual original graph/calendar/registry, `HybridProbabilities`, original rates and source mode. It marginalizes the once-drawn register using the second projection of the registered timed readout. The original register still governs the joint source law; it is not reset, fixed, redrawn per panel, or exposed to the observer.

Writing E for register erasure and P for ordinary timed pruning, the proof is the measurable pushforward identity

    (mu.map E).map P = (mu.map registeredPrune).map E.

Composing this identity with the existing actual natural all-panel G2 theorem yields the ordinary selected-source timed law. No desired coupling or observation equality is supplied as a new theorem hypothesis. The constant Unit register in one measurability proof is solely an injection into a product space, not a source modification.

The inherited forward G2 provider permits a sitewise mode function. The draft consequently has that stronger forward scope; this is NOT an expansion of the inverse G5 master beyond its accepted COMMON/INDEPENDENT contract. Empty/singleton panels retain the inherited conventions.

**Evidence category:** source-level proof draft and inspected provider correspondence. Not elaborated, kernel-checked or independently reviewed. It is a marginalization corollary, not a new stochastic process construction or the full inverse theorem.

### 2.2 Frozen three-lineage polynomial kernel

[sources/G5FrozenTriplePolynomialKernel.lean](sources/G5FrozenTriplePolynomialKernel.lean) supplies an explicit five-partition algebraic port, with the codes:

    0: 0|1|2    1: 01|2    2: 02|1    3: 12|0    4: 012.

For three surviving ancestral lineages frozen in one population at pair rate lambda > 0, put q = exp(-lambda*u). The probability of no merger is q^3; the probability of each specified two-block partition is (q-q^3)/2; and the probability of one block is 1-3q/2+q^3/2. They normalize, and positivity on 0 <= q <= 1 follows from

    (q-q^3)/2 = q*(1-q)*(1+q)/2,
    1-3q/2+q^3/2 = (1-q)^2*(q+2)/2.

For one colocated pair and an isolated third lineage, the only nonzero probabilities are q for the discrete partition and 1-q for that pair partition. Three different frozen populations remain discrete. After the first merger there are TWO live ancestors, so their merger rate is lambda, not two times lambda. Counting original descendant copies instead is rejected by the executed negative control.

The draft contains normalization, positivity, zero-time and endpoint identities, continuity/limit transport, an arbitrary finite-mixture endpoint identity, and positive occupancy-mass iff some positively weighted seed has that occupancy. The weights are NOT assumed to factor. Survival conditioning can change weights and induce dependence without deleting feasible routes from support.

**Exact limits of this draft:** its limit transport assumes q tends to zero. The substitution q=exp(-lambda*u), decay, the finite-mixture limit interchange and analytic germ uniqueness are explained mathematically here but are not all assembled as Lean declarations. The module does not define a source adapter that merely assumes the missing source-law theorem.

## 3. The next exact source-law implication

Fix three distinct original tips U, an original calendar time t >= 0, and the actual selected source law. Let E_U(t) be no selected merger by t. Let Z_t be the actual current ancestral population assignment immediately after the original instantaneous movements at t. Its partition pi(z) records only which selected ancestors occupy the same population. At most one occupied population contains multiple selected ancestors, so lambda_z is its actual pair rate; when all three are separate, the rate argument is unused.

The next required theorem must DERIVE, from the compiled original source and its clocks, the existence of an event-free epsilon > 0 and the identity, for 0 <= u < epsilon and each of the five partitions sigma,

    P(genePartition(t+u)=sigma | E_U(t))
      = sum_z w_z * row(exp(-lambda_z*u), pi(z), sigma),

where

    w_z = P(E_U(t) and Z_t=z) / P(E_U(t)).

It must also derive P(E_U(t)) > 0 and characterize exactly which original feasible no-merger routes have positive w_z. One cannot define the seed set as positive-mass states and then silently infer equality with all combinatorially feasible original routes. The original source/readout binding is precisely the missing obligation, not a new input field.

The G2 consumer makes ordinary selected-source laws available without observed registers. The next binding should use the actual current-ancestor merger catalogue and original event-free epoch, not just the pair route-survival formula. On E_U(t) the three selected ancestors have not merged. At later mergers the source must switch to its current ancestral owners while retaining old genealogy subtrees. The finite-clock Markov/memoryless argument must be connected to the actual G2 timed readout.

For the mathematical continuation, each frozen row is a finite exponential polynomial. Any two admitted frozen representations agreeing on the observed right-hand germ agree everywhere by analytic uniqueness, even with different numbers of hidden states, repeated rates, or equal cross-seed exponents. For each positive rate, q tends to zero. Taking the finite-mixture limit gives

    frozenLimit(sigma) = sum_(z: pi(z)=sigma) w_z.

Positive weights then recover the occupied-population partition SUPPORT. This recovers a functional of exact observed laws; it does not supply hidden population identities. The continuation to u=infinity is FROZEN continuation, not the actual network's long-time genealogy, which eventually enters the common ancestral population. No finite-data stability or uniform positive separation follows.

## 4. Full-master obligation register

| Obligation | Current status and remaining implication |
|---|---|
| G5-A: exact contract/readout/target | Human-readable canonical freeze above. Formal original M3 family and full cluster/split decoder binding still required. |
| G5-B: genuine arbitrary-weight timed source | Inspected G2 actual natural timed all-panel provider plus original positive coin/pair-clock components. New register-erasure consumer UNCHECKED. Full selected triple conditional source/kernel identity and all feasible-route positivity remain open in this assembly. |
| G5-C1: observed local support | Explicit five-state formulas symbolically checked; Lean polynomial/positive-mixture draft UNCHECKED. Actual conditional-source identity, exponential/mixture limits, analytic uniqueness and exact support readout remain to assemble. |
| G5-C2: safe chronology | Reuse historical safe-past disjointness, pair-only sure-block chronology and meeting permanence at their actual source scope. A deterministic sure-block predicate is not yet an observed-law predicate merely by naming it. |
| G5-D: deletion initialization/persistence | Prove complete original-X representative induction, attained sure-block times, original-tip deletion, recomputed ordinary marginals, full-switching persistence, both support directions and termination. Never carry the old no-merger posterior through a deletion. |
| G5-E: full target | Assemble all lifted rooted clusters, no false positives/no omitted clusters, positive original-edge interval witnesses and exact binary-root unordered split normalization. Fair-Q normalization alone is not a full-cluster certificate. |
| G5-F: threshold | Existing fair-M2 Q upper bound and actual max-one source counterexample remain accepted at their scopes. No M2 versus M3 lower bound for the arbitrary-weight full target is claimed. |
| HG: accepted bounded-indegree extension | Preserve categorical weights, original bridge-component position bound k and sufficient M_(k+1) full target. Existing exact-block theorem is reused. Binary G2 source types cannot silently serve as an indegree-k source instance. Categorical source/compiler and full stochastic/chronological assembly remain required. Use full-X law when the accepted HG contract has |X|<k+1, not an empty observation family. No k+1 optimality for genealogy laws. |
| G5-V: verification | No new Lean execution, no complete transitive axiom/dependency audit, no independent semantic acceptance and no whole-master closure. Source publication/readback and symbolic checks are separate evidence. |

A supporting draft or a completed symbolic check does not discharge this register. These are assembly debts, not a claim that every inherited component is absent or that the accepted hand theorem has been refuted.

## 5. Reuse-and-gap audit with exact identities

All paths below are in Commons unless an upstream pin is explicitly stated. They were read from the starting/current main snapshots; the input baseline was `f436b4f82b05bf2c99a55cbeeeb5dfb80265eca3`, and the pre-publication head observed was `5a94f375c9e5538da65b3d3ed05d4d6aa40177f6`.

- **Canonical M3:** `research/2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md`, git blob `1c047255686ce74e404976e1f3a5fff0b9944fa0`. Full document read. Nonplanar source contract `G5-NONPLANAR-CALENDAR-QUARTETS.md`, blob `3fbe07da7f30a43895b02e9b88bd6573d7ab3ede`, full read.
- **Older independent stochastic/chronology review:** `research/2026-10-01-dot-g5-independent-review-2005z/REVIEW.md`, relevant sections through the chronology and target discussion read. Its original accepted statement is planar M4, not the later nonplanar M3 endpoint. No full-tail read or new independent acceptance is claimed here.
- **HG:** `G5-HIDDEN-AMBIGUITY-BOUNDED-INDEGREE.md`, sections 1-6 inspected; final tail not fully read. Its categorical source theorem remains a separate formal obligation. `g7/G5BoundedExactBlock.lean`, blob `3923f1a5840ce7025e9e1ca88f8eaa70f2465daa`, fully read. Its bounded unary obstruction and `exact_block_iff_local` already supply the abstract k+1 combinatorics; not rebuilt here.
- **Historical safe-past:** `research/2026-10-02-dot-g5-safe-past-0518z/README.md`, blob `ee72428e88ceb4ee4d218b2c1b4a821be356128e`, full read. Its four-source inventory and recorded receipts are reused only as reported; the complete provider closure was not replayed here.
- **Fair normalization:** tested 825 package `fair-g5-normalization-v1/sources/G5FairNormalizedCutQuartetIdentification.lean`, blob `cf3752d2c3fb852e2c0b803cb872f4a7acc74b24`, recorded SHA256 `4cb9e6f925eb065b398bf4ba12c24fd40c4cf6b56892a461f454c19ca29a82f4`. Its endpoint explicitly uses fairParameters. It is not the arbitrary-weight full target.
- **Fair lower bound:** same package `fair-g5-sharpness-v1/sources/G5FairM2Sharpness.lean`, blob `97846003e3a309755995e8bb8cab127a0659756d`, and `SHARPNESS-SCOPE.md`, blob `6e91bf3f61bffacac61356be5eb0ac762c938733`, both fully read. The actual two quartet-tree sources match every empty/singleton calendar law and differ in normalized Q. Its dependency closure was not freshly reproduced.
- **Positive actual pair models:** baseline `UnifiedLean/Source/NativeIndependentPairMixture.lean`, blob `7d78743ea9639b8c98388abbc7c86414e101cbd8`, full read; `NativePairCalendarObservation.lean`, blob `da17dd35ff22b7b82921946a97e456c5d5cfd9bc`, first 230 lines read; `NativeFairSelectorAssembly.lean`, returned description/site/fair-moment portions inspected. Do not count a pair survival identity as an all-copy timed law.
- **Selected current G2:** `research/2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2ActualTimedAllPanelLaw.lean`, blob `161f963dfdb12877f0630990a1a1baa93230fbee`, recorded SHA256 `05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376`, fully read. The exact actual-natural theorem retains `(V -> Bool) x TimedObservation Copy` before our marginalization. `G2TimedOutputForgetting.lean`, blob `60ad5b5c018db5d60a8d7c84f1b5bddb40d93f63`, was fully read: it forgets time as well as the register and is not the same observation port. README and PUBLIC-SOURCE-CONTEXT.json were fully read.
- **G2 dependency identity:** retain the 09:41 nine-consumer context and additive `G2CompleteTerminalReadout.lean` SHA256 `f7235d98732b30f3041e15d076ceb07771bd5c33879b8755550e724e0f0dfab8`. Its direct base is `G2CompleteTimedSupport.lean` SHA256 `169d7ce5aca559aec2016f8fe50a26629b2a24d94b135885d148f78e4cecb808`, public at commit `2dfd8b47bf22bbd9b56ec4ca0e177ccdc3d18ee5`. Those upstream SHA256s are recorded manifest identities, not freshly recomputed transitive-object evidence in this runtime.

No shared G2 source was edited. No new workers or workflows were launched. The complete dependency graph still needs reconstruction at the pinned context before running the consumer.

## 6. Executed evidence and reproduction

[The exact symbolic receipt](evidence/frozen-triple-symbolic.json) records Python 3.13.5, SymPy 1.14.0 and the actual 13:09:55 UTC PASS. It includes 25 forward-ODE coordinates, 25 initial coordinates, 25 infinite-time coordinates, 25 generator row sums, five normalizations, two polynomial factor identities, 45 exact rational posterior families and 225 endpoint-support checks. Negative controls reject original-descendant-copy rates after merger, zero-rate absorption, and zero-weight support preservation.

The generator is independently constructed from mergers of CURRENT partition blocks inside a fixed hidden population assignment, rather than copied from the proposed differential equations. The test is exact symbolic algebra for the finite three-label kernel, plus rational controls. It is not a full original-network control suite, a Lean kernel proof, a source-identification theorem or a numerical reconstruction of an observed germ.

From this packet, with the tested Python/SymPy environment already available:

```sh
python checks/check_frozen_triple.py
```

The new output timestamp changes. Compare checker hash, PASS status, counts and symbolic residual outcomes with the preserved receipt. No network access is required by the checker.

[Runtime evidence](evidence/runtime.json) records no lean/lake on PATH, no compiler job and zero Lean passes. Earlier direct GitHub access from the container failed DNS; the connected GitHub channel remained usable. A limited filesystem search found no runtime in its searched locations. This is an observed local blocker, not a mathematical obstruction or proof that no execution service exists anywhere.

The [connected modular workspace](../2026-10-05-dot-connected-modular-lean-workspace-2252z/README.md) was read before attempting further installation. It requires an existing Linux Lean 4.33.1 runtime at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, compiler binary SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, and already-built Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Its ordinary controls are serial, 180 seconds and 4096 MiB. Do not silently escalate or modify an input tree during a build.

The polynomial module has only Mathlib imports and can be checked independently once the pinned runtime exists. The actual-source consumer additionally requires the exact selected G2 dependency context. This packet does not invent a `lake test G5` target, contain compiled objects, reconstruct the complete import closure, or claim a turnkey fresh replay. Preserve actual compiler logs, full declaration/dependency inventories and axiom outputs when executing. A source token scan found no sorry/admit/axiom/native_decide outside comments in these drafts, but such a scan is NOT elaboration or a transitive axiom audit.

## 7. Published-source fingerprints

These source fingerprints were computed locally from the delivered UTF-8 bytes. The source directory was read back at `dfe1eb8928300a393146fa4e441835e64afd6897` and both Lean git blobs matched.

| File | Bytes | SHA256 | Git blob |
|---|---:|---|---|
| sources/G5HiddenRegisterTimedProjectivity.lean | 6153 | a7e8ae569fc51d2d0365394e4776ab83c254a488ea507d2b582367f625c4acc2 | cbb2ec6c32439b26e0833c29329209b30314e294 |
| sources/G5FrozenTriplePolynomialKernel.lean | 6291 | cca82db4762ba06fe34a16d0659d91db1d9285676366a1d73c9a28851e968c47 | 2140fea9686852657dff17f17c979cd1e752eaba |
| checks/check_frozen_triple.py | 7354 | 60c0241e96951bc784c0d85a52556feb0ed92ea94c44c93048bf57691adf4d76 | aa6ff602f71bb166450980a5eea8673ef3c9b641 |
| evidence/frozen-triple-symbolic.json | 1531 | c81d193b693e1b93319d1abc8b034b2236bcdb1365cdd36fef054fc221df151c | 56f28b94af373278af2dd493fd7154c61c0c4eaf |
| evidence/runtime.json | 1203 | 0306112b188493ba1a23b0660bab3f9013b9598aea6693720a468f61622ee173 | 98d177b5aad103c905c1d8982283e6214afbad4a |

## 11. Process-integrity review

Strength: actual ownership/ACK and coordinator receipt, immutable source identities, direct theorem-body inspection, explicit historical/current scope separation, public source drafts and executed symbolic receipts. Limitation: no full imported dependency replay; several large historical sources were read only in stated ranges; new Lean was not checked; this contributor is not an independent reviewer of its own work. Fixes: reconstruct exact provider closure, compile serially, audit transitive axioms and obtain independent source-semantic review. No invented numerical process-integrity score is assigned.

## 12. Inference-robustness review

The explicit kernel argument tolerates arbitrary positive rates, equal rates across populations, repeated exponents and nonfactorizing posterior weights. It fails without positive rates or positive feasible weights, as the controls show. The decisive falsification test for the full bridge is an admitted original source/clock state whose conditional event-free timed readout disagrees with the proposed row, or an unproved source-to-feasible-support identification. Kernel acceptance of the two drafts alone would still not establish M3 full-target recovery. No statistical effect sizes, heterogeneity estimates, minimum panel threshold or robustness percentage is inferred from these algebraic checks.
