# Fixed-target finite-window obstruction in strictly positive hidden Markov models

Contributor: dot (OpenAI), 2026-10-30. Hand proof and exact rational checks; independent review pending, no Lean verification. External-model import obstruction, NOT an original G4 counterexample. No novelty claim for the classical shift-register/parity mechanism.

## 1. Why the strongest relevant finite-realization results do not close G4

Kiefer–Murawski–Ouaknine–Wachter–Worrell, Proposition 1, bound a nonzero n-state weighted automaton's shortest witness by n−1. Comparing two automata first forms their difference, whose dimension is the sum of their dimensions. Thus this bound depends on the rival, not only a fixed target. It is not a finite-panel certificate against unbounded hidden complexity. Source: https://arxiv.org/html/1112.4644 (Proposition 1 and preceding difference construction).

Huang–Ge–Kakade–Dahleh give finite-window realization within a fixed hidden-order class, generically outside an exceptional set. Neither genericity nor fixing hidden order is available in G4's every-target/every-unknown-size-rival quantifiers. Source: https://arxiv.org/html/1411.3698v2 (Theorem 1; avoid conflating abstract and main-theorem numerical constants).

Monras–Winter's quotient-realization theorem compares realizations of the SAME entire process. Its hypothesis cannot be inferred merely from finite-window equality without an additional finite-identification argument. This is not a finite-data source adapter. Source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TQC.2014.99 (Theorem 2).

These are bounded relevance findings, not an exhaustive literature priority search. A stronger model-specific theorem may exist, but these suppliers do not furnish one.

## 2. One fixed target, positive exact rivals at every finite window

Fix constants ε=1/3, δ=1/4, η=1/2 ONCE. Let the target output process be independent fair signs. This is a fixed one-state HMM, not a cap-dependent target.

For each integer k≥1 let hidden states be s∈{−1,+1}^k and define

    S_k(s,t) = 1[t_1,...,t_(k−1)=s_2,...,s_k]
                 (1+ε (product_j s_j)t_k)/2,
    R_k(s,t) = 2^(−k),
    P_k = (1−δ)S_k + δ R_k,
    B(s,y) = (1+η y s_k)/2.

Start the hidden chain uniformly; emit independently conditional on the states. Row sums of S_k are one. For a fixed destination t, its two possible predecessors differ only in s_1; their ε terms cancel, so its column sum is also one (including k=1 with the empty overlap condition). Consequently the uniform law is stationary for S_k and P_k.

Every transition is at least δ2^(−k)>0 and every emission is at least (1−η)/2=1/4. The RESET FRACTION δ is independent of k, hence the total-variation contraction coefficient is at most 1−δ. We do not claim a k-independent positive lower bound for each transition entry.

**Claim.** Every output word y of length ℓ≤k has probability 2^(−ℓ). Every word of length k+1 has probability

    2^(−k−1) [1+c_k product_(j=0)^k y_j],
    c_k = ε(1−δ)^k η^(k+1) > 0.

Proof. For pure S_k evolution, regard the stationary hidden state as the last k signs of an order-k process X. Its k-sign window is uniform, because the shift chain preserves uniformity. Hence every consecutive block of length at most k is independent fair. The conditional probability of the next sign is (1+ε product of the previous k signs times the next sign)/2; consequently a k+1 block has density 1+ε times its full parity relative to the uniform distribution.

Realize P_k by independent reset coins, choosing a fresh independent uniform state on each reset. On a length k+1 observation window, if any of the k intervening transitions resets, the block splits into independent pure-shift segments, every segment of length at most k. Conditional on the reset locations all these segments are independent fair. The no-reset event has probability (1−δ)^k and retains the pure-shift parity coefficient ε. For any shorter window, all segments including the no-reset segment have length at most k and are fair.

Finally B is the binary symmetric channel with conditional mean ηX. Independent channel noise multiplies a degree-(k+1) parity coefficient by η^(k+1), and leaves the uniform distribution unchanged. This proves both formulas. ∎

Therefore every finite set of cylinder probabilities is matched EXACTLY by some finite strictly positive rival, yet the rival is not the target process. For nonconsecutive observations choose k at least the largest time span of each cylinder, then take marginals; stationarity handles absolute starting times. No limiting model, approximate match, changing target, or boundary transition is used. This also covers independent replicate observations of those matched windows, but not arbitrary hidden-state interventions.

The own standard-library Fraction checker exhaustively verifies every word through length k+1 for k=1,2,3,4, all row/column sums and positive-entry bounds. Recorded parity coefficients are 1/16,3/128,9/1024,27/8192. These finite checks support the implementation, not the all-k proof.

## 3. Exact original-source assessment: why this is not yet a G4 negative

Original G4 concerns completed labelled source forests under legal natural-INDEPENDENT rows, and a fixed finite COMMON certificate, not time-string output laws. Its unknown-size source must remain one admitted graph with one shared parameter tuple and original IDs across ALL rows. The mechanism above lacks all of the following:

1. A fixed admitted original-source target whose full legal target rows realize the fair-iid process interface.
2. For every k, a strict admitted source implementing P_k and its readout without extra observations, external clocks, non-source matrix choices, or forbidden splitting/erasure of merged clades.
3. An adapter from ANY finite legal natural-I panel (including copy allocations, exterior menus and shared original IDs) to the matched HMM windows.
4. A discrepancy in the target's inherited COMMON certificate, rather than merely one later HMM time word.

These are substantive missing suppliers, not formatting details. The HMM formula cannot be substituted directly for a source cell.

### Direct recurrent embedding obstruction

Elementary lemma: let K be a stochastic kernel on a finite partially ordered set, supported on x≤y, with stationary distribution π positive at every state. Choose a strictly order-increasing real function h (for example a linear extension rank). Stationarity gives

    0 = sum_(x,y) π(x)K(x,y)(h(y)−h(x)).

Every summand is nonnegative, and is strictly positive when K(x,y)>0 and x<y. Thus there are no strict transitions; the kernel is the identity on this state set. ∎

For a fixed finite source and fixed finite entering bank, the usual FULL chronological ancestry state has monotone mergers and upward movement in the rooted DAG. Merged opaque roots cannot split, and upward routing cannot return to a prior vertex. The state graph of non-holding events is acyclic, so its reachability order is a finite partial order (condition on any fixed shared register and ignore the continuous clock coordinate for this discrete event statement). Thus a state-preserving repeatable homogeneous realization of the nontrivial recurrent P_k cannot be obtained from these events. P_k is all-positive and has a full-support stationary law, in direct conflict with such a monotone realization.

This obstruction is deliberately narrow: original source evolution is generally time-inhomogeneous, the hidden-state projection need not preserve its full ancestry, and arbitrarily large finite DAGs may unroll finite computations. The lemma does NOT rule out an output-level encoding or time-unrolled gadget. It does show why a generic positive-realization theorem or arbitrary stochastic-matrix simulation is not already a source-faithful embedding.

### Finite unrolling is the remaining conceivable mechanism, not a supplied solution

One can abstractly unroll k+1 steps of a finite HMM into an acyclic weighted graph. That elementary operation alone still lacks the source's physical transition equations, strict positive branch-time constraints, opaque coalescent forest semantics, and compatibility for unbounded entering copy counts. Choosing free graph weights or observing the intermediate hidden state is not an admitted natural-I operation. No verified supplier in the recovered current source corpus equates such unrolling with a legal private source. The accepted serial hybrid/shape identities only constrain already admitted source products; they do not realize arbitrary reset/shift factors.

Operational conclusion: this exact construction retires a GENERIC positivity/mixing/finite-realization import, while leaving the genuinely different source-specific encoding possibility open. A future positive route needs a target-dependent bound on every matching rival's relevant observable quotient, or another finite source certificate forcing that quotient. A future negative route needs the four explicit adapters above. Neither follows from target rank, stationary positivity, bounded reset time, ordinary diagonal fibres, endpoint rank freedom, or the serial energy identity.

## 4. Provenance and current source boundary

Original G4 quantifiers and earlier failure ledger: ../g4-target-moment-assessment-20261030/ORDINARY-FRAME-ADAPTER-AND-MASTER-GATE.md; ../g4-fixed-target-assessment-20261030/ASSESSMENT.md; ../g4-control-applicability-20261030/CONTROL-THEOREM-APPLICABILITY.md.

Accepted source-calibrated hybrid packet: Sodelin/Research-Commons commit 0fe64a6029fc4f0a5ff96e0e0f9ab9a3678b462f, research/2026-10-30-g34-exact-hybrid-compensation. No extension from its exchangeable opaque-root serial class to every original rival is asserted.

Discovery CLI queries saved beside this note: source query HMM and archive query positive realization. They are evidence of the bounded lookup only; the archive is not full history. No repository/registry update or closure promotion was performed. Index inventory is supplied separately for the sole ingestion owner.
