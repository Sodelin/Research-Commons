# Closure dependency audit and dominated-source statistical proof review

Historical preliminary audit. Its planned finite-target proof is superseded by [the complete dominated standard-Borel proof](dominated.md) and [actual-manuscript review](REVIEW-dominated.md). The dependency logic remains applicable; the word "planned" below is preserved rather than turned into a retrospective final-review claim.

Contributor: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Reviewed current local transfer_audit/README.md and its deterministic, adaptive, statistical and domain contracts. No commits; the statistical extension below is a review of the planned theorem, not a receipt that its final manuscript has been inspected.

## 0. Verdict

The completed general foundation does **not** establish the whole biological observation-fiber classification. It characterizes what an application must prove. The current README correctly leaves ALLLEVEL-STAT-01 open and distinguishes a hand-proved foundation from a source-faithful scientific bridge.

The user's new completion criterion is stronger than publishing a general theorem: both the registered master result and a specified downstream open problem using it must be established. That combined gate is not met by the present packet. Fix the downstream problem in advance; do not turn this into an obligation to solve every future problem that could ever use the foundation.

## 1. Why dependency is not sufficiency

For a biological model class Theta, let O(theta)=P_theta be its complete admitted observation law and g(theta) the requested network answer. General factorization says that a law-level decoder exists iff

    P_theta=P_theta' ⇒ g(theta)=g(theta').

It does not prove this implication for the biological class, compute its observation fibers, or identify the set of answers within an ambiguous fiber. Defining the answer set {g(theta):P_theta=P} is a specification, not an obtained classification.

A generic transfer theorem supplies a reusable inference rule. An application still needs a bridge B proving model membership, observation semantics and the target-preservation premises. Logically, M together with B can imply the application A; M alone does not. “A uses M as a critical lemma” is a proof dependency, not a claim that no other possible proof could solve A.

A collision for quartet marginals addresses those marginals. A complete-observation impossibility claim needs a collision of the complete declared laws. A valid whole-class counterexample refutes a universal positive recovery assertion, but does not automatically solve a separately registered whole-class fiber classification or characterize the extra information enabling recovery.

## 2. Finite, explicit closure gate

Freeze one master statement M and one downstream statement A (or an explicitly finite bundle), with their admitted classes, targets, observations, error/resource promises and closure types. The combined task closes iff every applicable gate has a concrete certificate:

| Gate | Required certificate | What does not close it |
|---|---|---|
| Master theorem | Exact hypotheses/conclusion and full-scope necessity/sufficiency, or the registered valid refutation | A special case replacing the master |
| Downstream openness | Prior-work comparison showing the precise remaining gap | Rediscovering known C4/C5 identification |
| Application membership | All admitted models map into the theorem's premises with correct target and observation contracts | Naming analogous quantities or assuming a quartet oracle |
| Premise discharge | Source-class proof of target invariance, simulator existence, or the corresponding sharp impossibility/identified-set result | Repeating the general iff |
| Application conclusion | Derivation answering A throughout its declared class | One positive instance or one collision when A asks for classification |
| Constructive promises | An effective procedure and defended noise/cost bounds if A promises an algorithm | An existential quotient whose computation presupposes the answer |
| Evidence and review | Source/model fidelity, independent proof review and relevant code receipts; empirical validation when an empirical claim is made | Treating finite checks as a universal proof |
| Scope invariant | No silent weakening of levels, blob count, observation richness, target or error guarantee | “All levels” only on a convenient substituted subclass |

Pure mathematical closure under an explicitly stated biological model does not require proving that the model is empirically true. A practical biological-effectiveness claim needs that additional evidence. Likewise an existential theorem need not supply an algorithm unless one was promised. These distinctions prevent adding new requirements after success while still preventing premature closure.

A closure certificate should name M, A, the bridge lemmas B, pinned proofs, reviewer verdicts, and any exact negative/abstention regime. If M is established but B or A is open, record “foundation complete; combined application target open.” New unrelated applications become new tasks; they do not reopen a correctly closed registered theorem.

## 3. Dominated-source extension: all-class proof audit

**Planned scope accepted.** X is an arbitrary measurable space; every P_theta is absolutely continuous with respect to one common probability measure mu; Y is finite and nonempty; Theta is arbitrary and nonempty. A common sigma-finite dominating measure may be replaced by an equivalent probability measure. The same domination must hold for the whole parameter class, not a separately selected measure per parameter.

Let p_theta=dP_theta/dmu in L1(mu). A finite-output kernel is represented by functions k_y in L∞(mu), k_y≥0 and sum_y k_y=1 almost everywhere. This kernel set C is a weak-star closed subset of the finite product of L∞ unit balls, hence compact by Banach–Alaoglu. Positivity is closed because it is tested by integrals against every nonnegative L1 function; the sum constraint is also weak-star closed.

For each theta, the vector with coordinates integral k_y p_theta dmu varies weak-star continuously. Therefore f_theta(k)=TV(KP_theta,Q_theta) is continuous. The supremum over arbitrary theta is lower semicontinuous and attains its minimum on C. Finite restricted minima at a common threshold have the finite-intersection property, so

    delta(E,F)=sup_(S finite subset Theta) delta(E|S,F|S),

with one minimizing kernel valid over the full class. This uses compactness, not sequential compactness or a parameter-by-parameter choice of simulators.

For finite S, the dual variables satisfy lambda_theta≥0, sum lambda=1, and 0≤v_(theta,y)≤lambda_theta. The payoff is bilinear and separately continuous in weak-star k and finite-dimensional (lambda,v). Sion minimax applies to the compact convex sets and gives

    delta(E|S,F|S)
      = max_(lambda,v) [
          sum_(theta,y) v_(theta,y) Q_theta(y)
          − integral max_y sum_theta v_(theta,y) p_theta(x) dmu(x)
        ].

The integral maximum follows by minimizing over each stochastic row. The lowest-index maximizing y is a measurable selector because Y is finite. The original identity-rule utility witness and the universal TV risk bound then give exactly the same all-bounded-finite-action Bayes-risk duality as in the finite-observation proof. Finite-support priors and the compactness step extend it to every parameter in the arbitrary class.

Finally choose measurable representatives of the finitely many k_y, collect their exceptional sets into one mu-null set, and assign a fixed probability vector there. This yields an actual measurable Markov kernel, independent of theta. Common domination ensures the repair changes no P_theta. No standard-Borel assumption on X is needed for this finite-output repair.

**Audit verdict:** the planned extension is sound at this full stated scope. It strengthens observation-space generality; it does not remove common domination, finite Y, or the application bridge obligations. It is an established functional-analytic comparison argument, not a new empirical cross-field law.

## 10. Sources inspected for the proof tools

- Sion, M. (1958), “On general minimax theorems,” Pacific Journal of Mathematics 8:171–176, DOI 10.2140/pjm.1958.8.171. Publisher primary PDF inspected, Theorem 3.4 and compactness corollary: https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf .
- Buttenschoen, A., instructor-authored MATH 725 “The Weak* Topology and Banach–Alaoglu,” especially Remark 2 on arbitrary nonseparable spaces. https://www.buttenschoen.ca/MATH725/duality/weak-star/ . Inspected the general compactness argument, not only its separable sequential version.

The extension's detailed calculation above is explicitly derived here. No exhaustive priority review is claimed.

## 11. Process integrity

Checked dependency logic and the actual packet's open/closed distinctions, then independently derived the planned extension's compactness, simultaneous-parameter compatibility, minimax payoff, measurable selector and representative repair. No canonical files edited, no empirical efficacy claim, no Lean execution. A final actual-manuscript review remains necessary before treating this as a receipt for the author's extension file.

## 12. Robustness

The positive dominated theorem depends on one common dominating measure and finite output. Dropping either invalidates this proof route; it does not by itself prove transfer impossible. Even a perfect general theorem leaves the biological premises unresolved. Closure must be evaluated against the frozen application claim, with no silent scope reduction and no infinite expansion to unrelated future tasks.
