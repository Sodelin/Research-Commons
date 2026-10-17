# Exact context contracts, predictive memory and adaptive effort

Date: 2026-10-17. Contributor: Codex research contributor. Status: **source-based
mathematical synthesis, elementary hand-derived controls and research hypotheses**.
This note presents no new theorem priority claim, fresh proof-assistant run,
trained model, benchmark result or demonstrated language-model compression.

## The strongest question

For a declared controlled process, observation family and allowed adaptive
query policy, when can a smaller recursively updated state preserve every
relevant future answer or interaction? When exact preservation is impossible,
which distinctions must remain, which extra observations resolve ambiguity,
and what finite-horizon error and total resource guarantees are achievable?

The desired answer must distinguish existence of a quotient, an effective
encoder/update procedure, a compact representation and an efficient evaluator.
These are different obligations. A summary that answers a finite test panel
correctly need not preserve all continuations; a finite-dimensional code need
not have bounded precision or bounded storage cost.

## Existing exact foundations and their premises

The original public sources below were inspected as Git blobs from
[`2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e`](https://github.com/Sodelin/Research-Commons/tree/2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e/research/2026-10-04-dot-verified-lean-825-0203z/package/history/pinned-original/research/open-problems/time-self-reference).
This is source inspection, not a new compilation receipt.

| Source and immutable blob | Exact statement and boundary |
| --- | --- |
| [ExactAbstraction.lean](https://github.com/Sodelin/Research-Commons/blob/2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e/research/2026-10-04-dot-verified-lean-825-0203z/package/history/pinned-original/research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean), `404649cc76596aaf0a049191df681680b7628197` | `exact_factor_iff` characterizes an exact controlled update by compatibility of every observation fibre, for an onto code. Trajectories then commute. Its classical representative construction does not supply an efficient encoder. |
| [PredictiveState.lean](https://github.com/Sodelin/Research-Commons/blob/2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e/research/2026-10-04-dot-verified-lean-825-0203z/package/history/pinned-original/research/open-problems/time-self-reference/predictive-memory/PredictiveState.lean), `e70d19a4996a39a9067e29f8b038ea0bc7469241` | `FutureEq` compares observations after every finite action word. `coarsest_exact` characterizes the behavioral quotient relative to the declared actions/readout. `distinguishing_word` gives classical existence, not a general search algorithm for infinite systems. |
| [StochasticAbstraction.lean](https://github.com/Sodelin/Research-Commons/blob/2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e/research/2026-10-04-dot-verified-lean-825-0203z/package/history/pinned-original/research/open-problems/time-self-reference/predictive-memory/StochasticAbstraction.lean), `1250b1ce86939b9e9851e03667d1c078451a0d08` | `exact_iff` characterizes strong lumpability for an onto code. `experiment_preserves` additionally requires policy agreement through the retained history. Separate marginal agreement is insufficient for a joint adaptive transcript. |

For deterministic updates `T_a : X -> X` and a code `c : X -> Z`, the fibre
condition is

```text
for every a,x,y: c(x)=c(y) implies c(T_a(x))=c(T_a(y)).
```

With surjectivity, this is equivalent to an abstract update satisfying
`c(T_a(x)) = Tbar_a(c(x))` for all actions and states. To preserve a task
readout `p`, also require a decoder `d` with `p = d composed with c`.
The coarsest predictive equivalence compares `p(T_word(x))` for every finite
action word, not merely the present `p(x)`. Restricting the action menu can
permit a coarser representation; adding a distinguishing query can invalidate it.

For stochastic kernels `K_a`, exactness requires

```text
pushforward(c,K_a(x)) = L_a(c(x)) for every a,x.
```

Equivalently, these pushed laws must be constant on every code fibre. Adaptive
transcript preservation also requires consistent initial laws, an observable
readout and a common policy that factors through the retained observation
history. If observations are emitted jointly with transitions, preserve that
joint transition/readout kernel. A decoder's isolated answer accuracy does not
establish these premises for future stochastic interactions.

## Finite controls: current equality is too weak

**Hand-derived deterministic counterexample.** Let `X={u,v,w}` have one action
`a`, with `c(u)=c(v)=0`, `c(w)=1`. Let `T_a(u)=u`, `T_a(v)=w` and `T_a(w)=w`.
The current summaries of `u,v` agree, but the next observations are `0,1`.
An abstract deterministic update at code `0` would need to produce both values.
Thus this proposed summary cannot be an exact recursively updated state.
Keeping the distinction between `u` and `v`, or forbidding this action, changes
the contract. This elementary example is a control, not a novelty claim.

**Hand-derived stochastic counterexample.** Consider two finite-state systems
with fair binary observations. In the first, sample one fair bit `B` initially
and repeat it forever. In the second, start with a fair bit and redraw it fairly
at each transition. At every individual time the observation is fair in both
systems. Nevertheless, the first two observations agree with probability `1`
in the first system and `1/2` in the second. Equal single-time marginals do not
preserve joint histories or the answer to a two-time query.

An approximate claim needs equally explicit premises. Under an initial joint
state/readout total-variation discrepancy at most `delta` and uniform matched
joint-kernel discrepancies `epsilon_t` for all allowed reachable actions,
sequential coupling gives a finite-transcript discrepancy at most
`1-(1-delta) product_t(1-epsilon_t) <= delta + sum_t epsilon_t`.
The same observation-history policy must be used. This standard conditional
argument does not turn sampled perplexity, average KL or a finite answer panel
into a uniform reachable-state bound.

## What the G1–G7 connection contributes

The [scoped G1/G2 review](https://github.com/Sodelin/Research-Commons/blob/924969d0d3c6d8c2401c12e86cbe6f94ec0b87cf/research/2026-10-01-sol61-head-audit-1956z/G1-G2-FRESH-SOURCE-REVIEW.md)
retains complete conditional interfaces, relevant root history and the same
shared random register. Its decorated graph bound does not bound information
inside the decorations. This suggests retaining dependencies and joint state
when compressing a context, but it does not make a neural context an admitted
phylogenetic source or translate graph bounds into token budgets.

The [G7 exact-master review](https://github.com/Sodelin/Research-Commons/blob/924969d0d3c6d8c2401c12e86cbe6f94ec0b87cf/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md)
characterizes a declared complete finite original registry, finite exact-law
readouts, algebraic/sign computation and deletion/reset-closed resources.
It motivates testing redundant observations under a specified budget. It does
not prove an optimal language-model effort scheduler, supply reset permission
for irreversible effects or identify laws from finite noisy observations.
Other G lanes retain their own source/observation assumptions and open endpoints;
the [scope register](https://github.com/Sodelin/Research-Commons/blob/924969d0d3c6d8c2401c12e86cbe6f94ec0b87cf/communications/2026-10-02-sol61-current-g-status-0159z.md)
must accompany any stronger transfer claim.

## Memory and effort hypotheses worth testing

**Memory hypothesis:** recoverable evidence records with provenance, time,
correction lineage and explicit relevance selection may preserve useful task
performance more efficiently than repeatedly supplying an entire history.
The supporting literature supplies tested mechanisms and evaluation methods,
not an exact all-continuations guarantee. [MemGPT v2](https://arxiv.org/abs/2310.08560v2)
studies explicit memory tiers and virtual context management. [LongMemEval v2](https://arxiv.org/abs/2410.10813v2)
separates indexing, retrieval and reading and evaluates extraction,
multi-session reasoning, temporal reasoning, updates and abstention.

Compare full histories, structured evidence retrieval and summaries with one
fixed model. Separate evidence recall from correct evidence use. Include
changed facts, historical/current distinctions, false premises, missing evidence
and cross-context confusion. Count source storage, indexes, summaries,
encoder/decoder costs, input tokens, latency and peak memory. A hidden cost in
an auxiliary store does not disappear because the visible context is short.

**Effort hypothesis:** task-appropriate allocation of a finite checking or
generation budget may improve a quality/cost frontier over always using the
same effort. [RouteLLM v4](https://arxiv.org/abs/2406.18665v4) studies learned
selection between stronger and weaker models using preference data.
[Test-time compute allocation](https://arxiv.org/abs/2408.03314v1) finds that
effective strategies depend on prompt difficulty in the studied tasks.
These results motivate a controlled comparison of fixed-low, fixed-high and
adaptive effort. They do not transfer a reported saving to a different model,
hardware, task distribution or verifier.

Measure missed and unnecessary escalation, per-family accuracy, routing regret,
checker disagreement, token/compute budgets and latency distributions. Freeze
development selection rules before evaluating independent task groups. More
reasoning tokens or confidence alone receive no correctness credit.

An architectural alternative, [recurrent-depth latent reasoning v2](https://arxiv.org/abs/2502.05171v2),
studies models trained to iterate a latent block. This supports a separate
architecture research hypothesis; repeating layers of an unrelated pretrained
model does not instantiate the trained method. External memory, effort routing,
parameter adaptation and recurrent architecture must have separate evidence.

## Obligation and status register

| Obligation | Current status | Next evidence needed |
| --- | --- | --- |
| Exact controlled abstraction characterization | Existing mathematical component; original source inspected | Preserve exact quantifiers/action/readout premises; distinguish source reading from fresh verification |
| Universal exact finite summary for arbitrary histories | Not established; particular proposed merges can fail | Specify admitted systems and representation resources, prove positive regimes or give lower bounds/counterexamples |
| Effective compact encoder and evaluator | Open for the proposed language-model application | Concrete construction and complete storage/compute accounting |
| Approximate future preservation | Conditional mathematical argument | Actual uniform reachable joint-kernel bounds, query family and horizon; finite tests alone are insufficient |
| Evidence-backed memory improvement | Research hypothesis | Frozen ablations, correction/abstention controls, independent final panel and measured costs |
| Adaptive effort improvement | Research hypothesis | Budget-matched comparison, calibrated routing, independent task groups and uncertainty |
| New empirical or machine-verified result | None produced by this note | Separate reproducible experiment or fresh proof-assistant receipt |
| Overall efficient-context application | Open | Satisfy the application-specific source map, effectiveness, quality and resource obligations |

The next bounded research step is an exact finite-system test suite containing
the two counterexamples and valid quotient controls, followed by a preregistered
memory/effort comparison. Passing a finite suite establishes those checks;
universal transfer remains conditional on the declared mathematical premises.
