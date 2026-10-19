# Positive minimal-realization import: exact counterbridge and failed direct forest embedding

19 October 2026. Contributor: dot (OpenAI). Status: new hand argument and bounded rational controls, submitted for review. No G4 result, historical novelty, or Lean claim. Do not publish as master progress. Current research scope and ownership are unchanged.

## Attempted bridge and actual primary supplier

Attempt: infer a finite observation horizon depending only on the fixed target's minimal realization dimension, using strict positivity and uniform mixing to eliminate hidden higher-dimensional rivals.

Stefan Kiefer, Notes on Equivalence and Minimization of Weighted Automata (2020), Section 2, Proposition 2.2 and Theorem 2.3, directly read:
https://arxiv.org/html/2009.01217v1
The equivalence test uses both supplied realizations. The distinguishing-word bound is n1+n2−1. It does not depend on the target dimension alone. Its algorithm explores actual state-vector spans, unavailable from a finite observation panel alone. The classical linear-realization theorem is correctly credited there to earlier automata work. This pass makes no novelty claim for the following elementary hidden-memory construction.

Unlike a signed polynomial perturbation, the counterbridge below preserves stationary stochastic laws, strictly positive transitions and emissions, one fixed target, one tuple per rival, and a dimension-independent Doeblin mixing coefficient. It disproves the proposed target-only import even with those hypotheses. It is not an original G4 source.

## 1. One fixed target and strictly positive rivals

The target is the stationary fair independent binary process, with values in {−1,+1}, realizable by one hidden state. Fix three rational constants, independent of L:

    0<alpha<1, 0<delta<1, 0<eta<1/2.

For every integer L>=1 let the hidden states be x=(x1,...,xL) in {−1,+1}^L. Define a shift transition P0 by appending b with probability

    P0(x,(x2,...,xL,b)) = [1+delta b product_i xi]/2.

All other P0 entries are zero. Let U be the matrix all of whose entries are 2^(−L), and put

    P=(1−alpha)P0+alpha U.

Start in the uniform hidden-state distribution. At each time emit the last hidden bit, independently flipped with probability eta. Thus emission probabilities are eta and 1−eta, both strictly positive. Every transition entry is at least alpha 2^(−L)>0. Each row sums to one. For each new state z, the two P0 predecessors differ only in their oldest bit; summing their probabilities cancels the signed parity term. Hence P0, U and P preserve the uniform distribution.

The reset realization of P is literal: with probability alpha discard the old hidden state and draw a new uniform state, otherwise apply P0. These reset decisions are independent across time. A common reset couples any two hidden chains, so their total-variation distance after t steps is at most (1−alpha)^t. This is a dimension-independent mixing bound. It is NOT a lower bound on every matrix entry independent of the dimension; the entry lower bound above scales as 2^(−L).

## 2. Exact equality through L and first differing law

Under stationary P0 evolution, any L consecutive last-bit outputs form the hidden state at the end of that interval and are therefore uniform. For L+1 consecutive outputs v1,...,v_(L+1), their exact law is

    2^(−L−1) [1+delta product_i vi].

Condition on reset locations during an observed interval of length n<=L. They divide it into independent segments, each beginning with a uniform hidden state and each of length <=L. Every segment is uniformly independent in its output bits, so the whole interval is uniform. Independent output flips preserve uniformity.

For an interval of length L+1, every reset pattern with at least one reset likewise gives independent uniform segments. The no-reset event has probability (1−alpha)^L and the P0 law above. Applying independent bit flips multiplies its sole nonconstant parity coefficient by (1−2eta)^(L+1). Consequently the emitted word law is exactly

    Pr(Y1=y1,...,Y_(L+1)=y_(L+1))
      =2^(−L−1)[1+c_L product_i yi],
    c_L=(1−alpha)^L delta (1−2eta)^(L+1)>0.

All shorter word probabilities equal those of the same fixed fair-iid target. Every finite set of time-coordinate observations is covered by a sufficiently long finite interval and therefore can be matched by selecting L at least that interval's length. The rival is nevertheless inequivalent. No approximate matching argument is used. Both the full word law and its parity difference are explicit; no scalar-only moment matching is substituted within this HMM claim.

Thus fixed target rank one, stationarity, strict stochastic positivity and even uniform Doeblin mixing do not imply finite target-specific determination among all finite HMMs. One cannot remove n2 from the supplier merely by adding these conditions. This does not refute a theorem imposing further source-specific restrictions.

## 3. Actual forest-source comparison and failed direct embedding

Original source Sections 1–3 were retrieved and directly read in this pass, alongside the saved dormant-cell derivation:
https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md

The original natural-INDEPENDENT cell routes every current root independently with a common coin parameter, including each opaque already-merged subtree; coalesces within arms for positive durations; and reunites the resulting full rooted forests. The tuple is shared across all rows. Sampling rows are original legal forest observations, not observations of an arbitrary sequential hidden symbol process. Accepted G4 requires one fixed strict target and all permitted finite unknown-size rivals, with exact full-law agreement; a counterexample in a broader probabilistic class cannot replace this.

A direct state-by-state embedding of the displayed HMM fails a concrete structural condition. At fixed root cap, complete forests can only advance by mergers/grafting; an already merged subtree is never split or erased. Let F<=G denote that G is obtainable from F by such merges. This is an antisymmetric relation on the complete labelled forests. If an injective map x->F_x represented the HMM's transitions by actual forest transitions, positivity of P(x,z) and P(z,x) for distinct states would force both F_x<=F_z and F_z<=F_x, hence F_x=F_z, a contradiction. The HMM reset and shift discard/rewrite hidden bits; forest coalescence preserves its opaque merger history.

Mapping all HMM states to one forest avoids that contradiction only by losing the hidden-state-dependent emission. Adding an observable last-bit emission by hand is outside the original grammar. This excludes only this direct Markov-state/forest embedding. It does not exclude a more sophisticated finite-horizon compiler, a different topology for each cap, or a different exact-rival construction. Nor does it exclude source-specific finite forcing.

A valid use toward negative G4 would therefore require an actual compiler mapping these joint finite laws into legal independent forests with one admitted shared positive tuple and uniform exposure reserve, plus a later distinguishing original row. No such compiler follows from finite stochastic realization or from the direct construction. A positive G4 route must exploit the forest-source structure absent from generic strictly positive HMMs, rather than assume positivity removes hidden high order.

## 4. Prior coverage and exact outcome

The saved ANALYTIC-FULL-FOREST-ACCESS-GATE.md already rejects fixed-order recurrence bounds whose order grows with the rival. CONVEXIFICATION-PRIOR-STOP.md already distinguishes external shared selectors from independently routed current roots. This pass does not supersede either. Its additional concrete evidence is the strictly positive, uniformly mixing, same-target delayed-law counterbridge and the explicit failure of its direct forest-state embedding.

The adjacent check.py uses exact Fraction arithmetic with alpha=1/3, delta=1/2, eta=1/4, for L=1,2,3,4. It checks strict positivity, row sums, stationarity, and every word through L+1 against the formula. check.log reports PASS. These controls do not prove the all-L assertion; Sections 1–2 provide that proof. No original forest rival or full G4 certificate was executed or constructed.

Outcome: the attempted minimal-realization import fails at a real mathematical implication, even before original-source admission. Full G4 remains open at the exact source-preserving finite-fibre bridge. No publication is proposed without review and a decision that this source-applicability boundary is worth preserving publicly.
