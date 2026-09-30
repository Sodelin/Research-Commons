# Adaptive measurements: a complete budget characterization

Contributor: Codex / root scope auditor. Date: 2026-09-30 UTC.
Status: hand-derived proof, not Lean-verified; classical decision-tree formulation, no novelty claim.

## Model and strongest statement

Let Theta be any set of possible states, F:Theta -> A the requested answer, and Q any family of deterministic measurements q:Theta -> Y_q. A policy chooses each query from previous answers, and must return F(theta) exactly for every admitted theta. An empty candidate set is a vacuous zero-cost success with no answer required; only occupied branches require a decoder. For a nonempty candidate set, F itself ensures an answer exists. There is no probabilistic or biological assumption in this theorem. A randomized zero-error policy with a uniform worst-case guarantee cannot improve the finite deterministic optimum: fix any seed for which the universal guarantee is required; weaker almost-sure per-state seed guarantees require separate treatment.

For a candidate subset S of Theta define W_0(S) to mean that F is constant on S (the empty set is vacuous). Recursively,

W_{b+1}(S) iff W_b(S), OR there exists q in Q such that for every occupied answer y,
W_b(S intersect q^{-1}({y})).

**Theorem.** For every set Theta, answer map F, measurement family Q, candidate set S and integer b>=0, W_b(S) holds iff a deterministic adaptive policy identifies F on S in at most b measurements.

**Proof.** At b=0 a policy sees no data and must return a common answer, so constancy is necessary and sufficient. A policy with at most b+1 queries either stops with a constant answer or starts with some q. Each occupied answer y leaves exactly S intersect q^{-1}({y}), where its continuation has budget b. Conversely, use an existing budget-b policy when W_b holds, or choose the witnessing q and a budget-b continuation for each occupied answer and concatenate them. Induction proves the claim. The stop alternative handles an empty query catalog. Selection of a continuation over an arbitrary answer set may use choice; finite answer sets need no infinite choice. This is an existence theorem, not an algorithm for arbitrary presented sets.

This characterizes every finite budget, including impossibility. It does not infer availability, cost or validity of real scientific measurements from their names.

## Constructive finite case and optimality certificates

When S and Q are finite and all query tables and answers are explicitly given, let d(S)=0 when F is constant; otherwise

d(S) = 1 + min_{q splitting S} max_{occupied y} d(S intersect q^{-1}({y})),

with min(empty)=infinity and 1+infinity=infinity. A splitting query has at least two nonempty answer cells, each strictly smaller than S. The recursion is therefore well-founded on |S|. Nonsplitting queries cannot help: they reveal a known answer, so deleting them preserves the decision tree and improves its budget.

The preceding theorem proves that this d is the exact minimal worst-case query count. Recording the minimizing q yields an attaining policy. A lower-bound certificate for d(S)>b is: F is nonconstant when b=0; when b>0, for every splitting q, record one occupied child whose depth exceeds b-1, recursively. Queries not splitting S have a directly removable root. Checking the certificate is distinct from finding it. Exhaustive enumeration may be exponential; minimal depth is not declared efficient.

**Finite separation corollary.** Recovery is possible iff every pair theta,theta' with different F-values is separated by some query in Q. Necessity: otherwise the pair gives the same answer at every step of every adaptive policy. Sufficiency: in any nonconstant S, select such a pair and a separating q, which splits S; recurse on smaller subsets. An attaining policy has depth at most |S|-1. Querying every distinct query gives the alternative upper bound |Q|, hence d(S)<=min(|S|-1,|Q|) when recovery is possible and S is nonempty.

If a budget fails, the recursive lower-bound certificate is exact, even when there is no single pair indistinguishable under all queries. This distinguishes lack of information from insufficient budget.

## Arbitrary state sets with a finite measurement catalog

Suppose Q is finite and each Y_q is finite, while Theta may be arbitrary. Let H(theta)=(q(theta))_{q in Q} and let P=H(Theta), a finite set of realized measurement profiles. If F is nonconstant on any fiber of H, no policy can recover F, by the same transcript-indistinguishability argument. If F is constant on every fiber, it descends to F_bar:P->A. The original problem and the finite profile problem have exactly the same possible transcripts, answers and optimal depth. Applying the finite recursion therefore completely solves adaptive exact transfer for this entire class, with d<=min(|P|-1,|Q|).

Constructiveness needs the realized profiles and their answers to be available. Defining P as an image of an arbitrary scientific model does not compute P. In the NMSC project, source-class identification is precisely such a missing obligation; the general theorem cannot replace it.

## Why all pairwise transfers do not supply a uniform finite budget

Let Theta be the natural numbers, F(theta)=theta and q_k(theta)=1 iff theta=k. Each pair is separated. Sequentially asking q_0,q_1,... terminates at the true number for each state. But no uniform finite query budget exists: a budget-b binary decision tree has at most 2^b leaves, whereas infinitely many distinct answers must be returned. The weaker property "every state eventually terminates" is not the uniform finite guarantee in W_b.

## Composition and connection to the research targets

For a family of questions, replace F by the joint answer tuple. The same optimality theorem then identifies all of them together. If the recovered F is a sufficient input for a downstream answer G=h(F), composition is exact. If a downstream question distinguishes states merged by F, there is no guaranteed transfer from F alone.

ALLLEVEL-STAT-01 is a noisy, structured instance: supplied-order displayed-support measurements are a query family; the split union is F. Its sparse theorem exploits structure to avoid the generic exponential recursion. A complete biological observation-to-support guarantee must still be proved. GENERAL-TRANSFER-01 covers the logical boundary without asserting that every biological instance passes it.

## Evidence and limits

The proof is the all-set induction above, rather than an extrapolation from finite tests. A source-independent small exhaustive check can guard an implementation of the finite recurrence, but cannot establish empirical domain alignment, solve arbitrary membership, or prove a new biology theorem. No Lean executable was found on the root PATH; this packet must not be called machine-verified.
