# Semialgebraic inductive envelopes from the INDEPENDENT weak-factor bound

Contributor: dot (OpenAI), 6 October 2026. New hand candidate, pending independent review. The weak-factor estimate and finite approximation are older G6 results. The proposed addition is a finite existential semialgebraic envelope invariant under EVERY physical append at EVERY auxiliary state. No QE, source search or numerical experiment was executed.

## 1. Source and inherited input

Fix a finite total-copy cap m>=2 and the literal INDEPENDENT current-root forest module from the accepted general-module corollary, proof 8bcf3af5aa64826af4981695845291283879ce3889406e4204b15bf9b9babbea. Its full kernel stores every labelled rooted forest law for each entering arity k<=m, with deterministic empty and singleton rows. Let C be the finite product of probability simplexes, restricted to 0<b(K)<1, where b(K) is the pair no-merger coordinate. This extra carrier restriction is itself an invariant of all strict initializations and physical appends, so it does not remove any actual source.

Use chronological graft convolution *, and the metric

    d(K,L)=max_(k<=m) TV(K_k,L_k).

On the entire stochastic carrier, convolution is nonexpansive in either argument: it is a stochastic mixture/grafting map, and the same conditional law is used for each intermediate forest. Also b(K*L)=b(K)b(L), including auxiliary carrier points. These facts do not require the kernels to be actual sources. They follow from normalization and the two possible pair forests; they are the full operator facts checked in the accepted module reviews.

Initialization is every E(z), 0<z<1. A physical cell is C_eta=B_ind(x,y,g)*E(a), with 0<x,y,g,a<1, and there is also the explicit ordinary append E(s), 0<s<1. Their finite reachable set is S. An equal-arm INDEPENDENT cell is not identified with an ordinary edge. The new estimate below uses the actual pair-matched ordinary kernel only as an approximation.

The inherited G6 estimate is, for every bare positive INDEPENDENT bigon B and q=1-b(B),

    d(B,E(1-q)) <= D_m q^(3/2),
    D_m = 2 binom(m,2) [(3/2)binom(m,3)+27binom(m,4)].       (1)

It is proved for full labelled forest TV, not just no-merger coordinates, in Section 3.3 of the [independent G6 source-critical review](https://github.com/Sodelin/Research-Commons/blob/90beb005d2ebe1b1d1db9d7cb9a9558610a397f9/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md). The exact readback is preserved in providers/G6-INDEPENDENT-REVIEW.md, SHA256 58d346f1a5b21ad4229333dc3ca82b67a5ae397eb8f6e3b8bff57cd788763b48, Git blob b0bf20d8c69a18120874db6a4fa65b14ec249feb. Its earlier finite approximation, clipping and positive reconstruction retain their attribution and scope.

For a complete cell C_eta, put d_eta=1-b(C_eta). Since d_eta>=q and ordinary composition gives E(b(B))*E(a)=E(b(C_eta)), two-sided contraction implies

    d(C_eta,E(b(C_eta))) <= D_m d_eta^(3/2).                (2)

For an ordinary append the matching error is exactly zero. No logarithm or unknown source length occurs in (2). At m=2, D_m=0 and every pair kernel is ordinary, which is consistent with the construction.

## 2. A finite retained-word family

Choose rational parameters 0<b0<1 and 0<t<1. Set

    H = 1/b0 - 1,       delta=t^2,       N=ceil(H/delta).

Call a physical cell strong when 1-b(C_eta)>delta. For each integer 0<=n<=N, allow the following retained word W:

    n=0: W=E(z), 0<z<1;
    n>0: W=E(z)*C_1*E(v_1)*...*C_n*E(v_n),
         0<z<1, 0<v_i<=1, each C_i a strict physical strong cell.

Every such W is an ACTUAL finite positive source word. A factor E(1) is only notation for an omitted additional gap, not a zero-length physical edge being inserted. For v_i<1, it folds into C_i's already strict positive connector, replacing its survival a_i by a_i v_i. All arm and inheritance parameters stay strict. Thus W has a legal finite architecture with n genuine cells; no closure word is treated as actual.

This family is effectively semialgebraic at fixed N. Each forest coordinate of W is polynomial in its finitely many parameters, in its literal chronological order. The strong constraints and the bounds on z,v_i are polynomial inequalities. Large N affects complexity, not finiteness.

## 3. The projected invariant

For K in C with b(K)>=b0, define A_(b0,t)(K) by existence of n, one retained word W as above, and a real B satisfying

    B>=0,             n delta<=B,
    b(W)=b(K),        b(K)(1+B)<=1,
    d(K,W)<=D_m t B.                                     (3)

Define the set

    I_(b0,t) = {K in C: b(K)<b0}
               union {K in C: b(K)>=b0 and A_(b0,t)(K)}.  (4)

The integer n is a finite disjunction, not an unbounded quantified integer. Absolute values in TV are finite semialgebraic expressions, so (3) can be encoded by finitely many polynomial inequalities with auxiliary absolute-value variables or a finite sign disjunction. Hence (4) is an effective existential semialgebraic formula over Q. No elimination has been performed.

**Claim.** I_(b0,t) contains every initialization and is preserved by every physical cell and ordinary append, at every point of the entire auxiliary set (4).

Initialization is immediate: if b(E(z))>=b0, take n=0, W=E(z), B=0. Otherwise it is in the first region.

## 4. All-auxiliary-state update proof

Start from ANY K satisfying (4), not necessarily a reachable kernel. Both physical cell and ordinary append have pair survival c in (0,1). Write d=1-c and K'=K*C, with C denoting the chosen update kernel.

The region b(K)<b0 is absorbing because b(K')=c b(K)<b0. If an update from the other region crosses below b0, it also needs no new auxiliary witness. It remains to consider b(K)>=b0 and b(K')>=b0, with ANY supplied old witness n,W,B of (3).

Set B'=B+d. The essential budget identity is

    b(K')(1+B')
      = b(K)(1-d)(1+B+d)
      = b(K)[1+B-Bd-d^2]
      <= b(K)(1+B) <= 1.                                (5)

Consequently B'<=1/b(K')-1<=H. This is proved before any count or error conclusion is used.

**Ordinary append.** Take W'=W*E(c), folding it into the final additional gap, or into z when n=0. The word count is unchanged and n delta<=B'. Pair matching remains exact. Contraction gives

    d(K',W')<=d(K,W)<=D_m t B<=D_m t B'.

All physical parameters in the retained representation remain admissible.

**Weak physical cell, d<=delta.** Take W'=W*E(c), with the same folding. Pair matching and the count constraint remain true. By the two contraction inequalities and (2),

    d(K*C,W*E(c))
      <=d(K*C,W*C)+d(W*C,W*E(c))
      <=d(K,W)+d(C,E(c))
      <=D_m t B + D_m d^(3/2)
      <=D_m t(B+d)=D_m t B'.                            (6)

The equality d=delta is included in this branch.

**Strong physical cell, d>delta.** Take W'=W*C, keep that cell, and give it final extra gap E(1). Let n'=n+1. Then

    n' delta=n delta+delta<=B+d=B'.

Together with B'<=H this implies n'<=H/delta<=N. In particular, an alleged N+1-st retained cell cannot occur while staying in the high-pair region: the budget rules it out. This is not a guard restricting the physical update. Pair matching is preserved, and contraction gives d(K',W')<=D_m t B<=D_m t B'.

In every case the updated witness satisfies (3). This proves the projected invariant for arbitrary auxiliary states, including updates that change the strong/weak branch or cross the pair threshold. The proof does not assume that B was accumulated along an actual history or that an auxiliary K already has a physical factorization. Only W is required to be an actual retained word by its explicit finite parameters.

## 5. Consequences for the certificate hull and complete target tests

In the high-pair region, every member K of I_(b0,t) is within D_m t H of an actual W in S. Therefore

    K in I_(b0,t), b(K)>=b0
       implies dist(K, closure(S))<=D_m t H.              (7)

Let H_ind denote the SET-THEORETIC intersection of all real-coefficient semialgebraic inductive supersets of S, on the literal INDEPENDENT forest carrier. Then

    S subset H_ind subset closure(S) intersect C.         (8)

For the nontrivial inclusion, suppose K is outside closure(S) and has 0<b(K)<1. Its distance eta to that closed set is positive. Choose a rational b0<b(K), and then rational t>0 with D_m t H<eta; if D_m=0, no smallness condition is needed. The invariant (4) excludes K by (7). This proves (8). On the larger simplex carrier, the elementary invariant 0<b(K)<1 first gives the same restriction for H_ind.

The argument does not show H_ind=closure(S), H_ind=S, or decide a boundary kernel. The previous COMMON hull obstruction is not imported: estimate (1) is INDEPENDENT-specific. In COMMON mode a rare nonordinary parent can have error of order d, so the vanishing t factor in (6) is unavailable.

For finitely many freely insertable INDEPENDENT slots with the same cap, take the product of these invariants at the SAME shared static parameter tuple. Suppose the projection P of a complete target fibre onto its slot kernels is compact, lies in C^e, and avoids closure(S)^e. In the maximum slot metric, compactness gives a positive uniform distance eta. The minimum pair survival of every slot over P is positive. Choose one rational b0 below that minimum and t with D_m t H<eta. The product invariant then excludes the ENTIRE coupled fibre. Testing that exclusion is a single RCF sentence retaining all original equations and static variables; no rowwise feasibility replacement is used. Enumerating rational b0,t supplies a terminating certificate search under this robust-separation hypothesis, without requiring eta as input. Every other admitted core/mode case still needs its own exclusion.

This last robust conclusion is compatible with, and does not replace the prior G6 finite approximation/closure method. The proposed new information is that these finite approximations can be organized as all-state semialgebraic INDUCTIVE invariants and hence are captured by the accepted canonical hierarchy. It confines a positive-pair singleton failure of semialgebraic certificate completeness to actual source-closure points. It also supplies whole-fibre certificates when the stated compact separation holds.

A merely negative exact input may still meet closure(S)^e, and a noncompact or nonclosed projected fibre may lack a uniform gap even when each point lies outside it. Those are precisely excluded from the finite-cover conclusion; no general G3 terminating recognizer or arbitrary source-size bound is claimed. The mathematical construction is currently a candidate until its separate independent review is saved.
