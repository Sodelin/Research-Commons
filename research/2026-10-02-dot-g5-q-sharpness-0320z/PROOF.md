# G5 Q panel sharpness: a complete terminal-hybrid subfamily theorem

Contributor: dot, direct open-problem attack lane, 2026-10-02 03:30 UTC  
Status: hand theorem and original-source transfer accepted in [independent review](independent-review/REVIEW.md), with exact finite controls. The unrestricted binary G5 Q maximum-panel threshold remains in {2,3}.

## Result, exact class, and remaining question

Let N be a finite binary rooted-LSA temporal phylogenetic source with contemporaneous labeled tips, strictly positive original edge durations, and strictly positive constant pair-coalescence rates on each original population including the ancestral tail. Every hybrid has two incoming original edge occurrences and **its one outgoing original arc goes directly to a taxon tip**. Its private parent weights are (1/2,1/2). Rates may differ from edge to edge. Parallel edge occurrences, nonplanarity, and arbitrary finite level/taxon count are allowed. All laws use one fixed source and parameter assignment.

**Theorem.** Within this class, equality of the complete ordinary one-copy rooted calendar genealogy law for every two-taxon panel implies equality of the entire union Q of displayed unrooted resolved quartets. The conclusion holds within and across private common-site and live-ancestor independent inheritance. Consequently the sharp worst-case maximum panel size for Q within this subclass is two: ordinary quartet trees show one insufficient.

This is not a theorem for the full G5 class. In particular, nonterminal hybrids with a child subtree, stacked one-taxon hybrid gadgets, nonuniform parent weights, or other source/observation changes are not silently included. Nor does it recover rooted-cluster union or S: the accepted five-taxon triangle/star collision lies in this exact subclass and still has different cluster/S targets.

No gene-tree topology support is used as displayed-quartet support. ILS may give all gene quartets positive probability. Our input functional comes only from pair merger-time laws, and the final target is the original complete-switching displayed quartet union.

## 1. Route process and pair meeting

Every rootward tip route encounters at most one hybrid: it is that tip's own direct parent if hybrid. Above it every vertex has a unique ordinary parent. Distinct sampled taxa can never share a terminal hybrid child edge or its common coin. Thus the full one-copy route choices are a product of independent private binary choices under either mechanism. Choices can be sampled at the start, even though they are used only at the hybrid age. Each choice has positive probability and extends to a complete original switching.

For any selected pair x,y, let M_xy be the first age at which their unmerged routes occupy the same original population edge (or ancestral tail). Once they meet, they remain together forever: above any first meeting there are no hybrids on either route. Before M_xy the merger hazard is zero; afterwards it is always a strictly positive population-specific rate. Thus M_xy has a finite atomic probability law, since only finitely many routes and original ages occur.

At any age t, write S_xy(t)=P(T_xy>t), with T_xy the observed gene merger age. Take the older-side right germ in a sufficiently small interval with no original event after t. Conditional on each route assignment, an already-met surviving pair has one constant current rate λ>0, whereas a not-yet-met pair has merger probability zero throughout that interval. Consequently

    S_xy(t+s) = C_0(t) + sum_(distinct λ>0) C_λ(t) exp(-λs),  0<=s<ε,

with nonnegative coefficients and

    C_0(t) = P(M_xy>t).

No not-yet-met route has suffered any pair merger, so its entire unconditional routing probability contributes to C_0. No already-met route contributes a constant term, because its current rate is positive. Group equal rates without changing this fact.

Finite exponential functions at distinct exponents are linearly independent on every nonempty interval: differentiating at zero gives an invertible Vandermonde system (or the usual finite exponential-polynomial uniqueness theorem). Therefore the exact observed right germ uniquely determines its exponent-zero coefficient, even when neither the hidden rates nor a calendar cover are supplied. Equality of complete pair laws forces equality of C_0(t) for every t. Hence the full pair law determines

    F_xy(t) = P(M_xy<=t) = 1-C_0(t).

The older-side convention handles a meeting event at t itself: that route belongs to a positive-rate term, not C_0. Strict positive original durations ensure some ε>0. In a comparison, take ε smaller than the next event in either finite source. This is an identification theorem using an exact-law functional, not an implemented finite-data clock parser.

**Elementary homogeneous fallback.** If every population has the same unknown λ>0, T=M+Exp(λ). The ultimate exponential tail of S identifies λ, and the jump in merger density at m is λP(M=m). For λ=1 this is the exact shifted-exponential calculation used by both earlier terminal-hybrid searches and the accepted triangle/star collision. Arbitrary edge-specific rates require the right-germ argument above, not this shortcut.

## 2. Fixed-time reduction to four categorical distributions

Fix four original taxa a,b,c,d and an age t. Each sampled taxon's route has two equiprobable alternatives if it is hybrid, or one deterministic alternative otherwise. Their current population positions are either distinct or equal. Represent each label i by two conceptual occurrences of weight 1/2; a deterministic position is represented twice at the same position. Below a terminal hybrid its two route alternatives likewise occupy its one original child edge and are concentrated at that time.

Thus the eight occurrences induce some set partition Π, with each original label occurring exactly twice. If n_i(E) is label i's count in population block E, then independent source choices and permanent pair meeting give

    K_ij(t) := 4 F_ij(t) = sum_E n_i(E)n_j(E),  i!=j.

The pair law determines the six integer counts K_ij, each in {0,1,2,4}. Hidden population names and source graph are not decoder inputs.

The existence of a switching whose age-t population edge contains a,b but not c,d is exactly

    some E has n_a(E)>0, n_b(E)>0, n_c(E)<2, n_d(E)<2.

Choices for the four distinct taxa are private and independent; a witness therefore extends to a complete switching with positive probability. The complementary exact c,d block has the symmetric condition. Let W_ab|cd(Π) be the OR of these two conditions. This is an instantaneous original population-edge witness for the displayed quartet, not an ILS genealogy assertion.

## 3. A closed hand criterion from only the six pair counts

For the split ab|cd set

    u=K_ab, v=K_cd,
    (p,q,r,s)=(K_ac,K_ad,K_bc,K_bd).

Then W_ab|cd is false precisely when at least one of the following holds:

1. One of p,q,r,s equals 4
2. u=v=0
3. v=0 and u=1, and either p=r=2 or q=s=2
4. v=0 and u=2, and p=q=r=s=2
5. The versions of conditions 3 and 4 obtained by exchanging the two sides ab and cd

Otherwise it is true. This finite formula directly decides each of the three possible displayed-quartet edge witnesses from the observed pair meeting CDFs.

### Hand proof

Each label distribution is either concentrated at one population with probability one, or split equally over two distinct populations. A cross count of 4 means a cross pair are concentrated at the same population. That label on the opposite side then blocks every possible exact two-label side; condition 1 implies absence. If u=v=0 neither same-side pair can meet, proving condition 2.

Suppose u,v>0. If an ab witness fails, every position in S_a∩S_b is forced by a concentrated outsider c or d. Choose one such position e; say c is concentrated there. Since v>0, d also has e available. For the cd witness to fail at e, a or b must be concentrated there, giving a cross count 4. Conversely condition 1 already implies absence. Thus outside condition 1, both positive same-side counts guarantee a witness. This argument uses only positivity of categorical weights.

It remains to consider u>0,v=0, up to exchanging sides. If a or b is concentrated, their intersection has just its forced position e. Blocking the ab witness requires c or d to be concentrated there, which gives cross count 4. Outside condition 1 this case always has a witness.

Otherwise a and b each split equally over two positions. If u=1, their support intersection is exactly one position e. Its witness is blocked precisely when c or d is concentrated at e. This is equivalent to that outsider having both cross counts 2: a split outsider with count 2 against a must have exactly S_a, and count 2 against b must have exactly S_b, impossible because their intersection has size one. Hence condition 3 is exactly the obstruction.

If u=2, their supports are the same two-point set {e,f}. Failure requires one outsider concentrated at e and the other concentrated at f. This implies all four cross counts 2 and v=0. Conversely count 2 against a's uniform two-point distribution forces an outsider's entire support into {e,f}; v=0 makes the two outsiders disjoint. Both are therefore concentrated at different positions, giving exactly condition 4. These exhaust u>0. The exchanged conditions exhaust v>0,u=0. The proof is complete.

## 4. Source-to-displayed-Q transfer

A retained original population edge with a,b as selected descendants and neither c nor d induces ab|cd in that complete switched tree after pruning and unary/root suppression. Conversely if a complete switched tree displays ab|cd, one of its rooted edge clusters, restricted to these four labels, is exactly {a,b} or {c,d}. The edge in the reduced tree comes from a positive path of retained original edges. At least one original edge on that path has the same selected descendant set and a nonempty calendar interval. Choose an age inside it to obtain W_ab|cd. The binary-root-suppression case is covered by choosing either side's rooted child edge.

Every chosen switching has positive probability, and every witness extends to all unsampled taxa. Therefore

    ab|cd is in Q(N) iff there exists t>=0 with W_ab|cd(K(t)) true.

Equal pair laws give equal K(t) at every age, hence equal W and equal Q. This proves the theorem independently of any bound on original network size or clocks. The finite K(t) step functions could be read on their actual change cells, but no arbitrary-law extraction algorithm or calibrated DNA estimator is asserted.

Common and independent inheritance give the same one-copy process here because no hybrid has more than one sampled descendant before its choice, even when the full original locus is sampled. Selected-label restriction preserves the same fixed original parameters. No common-mode correlation assumption beyond private independent site coins is added.

## 5. Exact controls and why this is stronger than earlier screens

`pair_quartet_kernel.py` enumerates every set partition of eight distinguishable occurrences by restricted-growth strings, with no calendar/tree sampling. There are exactly Bell(8)=4,140 partitions, 403 different six-count vectors, and zero fibers containing different W masks. The closed hand criterion is checked on 12,420 split predicates. An independent checker uses direct set-partition construction plus every one-occurrence-per-label selection as its witness oracle, rather than importing the contributor code.

This finite domain is complete because the source argument already bounds the queried four-label position description by eight equiprobable occurrences. It therefore eliminates the **entire equal-weight terminal-hybrid search family with arbitrary clocks**, not just the prior 11,550 min-height trees or 135,135 weighted-occurrence min-height trees. The new hand proof removes reliance on the finite check for the mathematical assertion; the exact enumeration is corroboration.

## 6. Exact obstruction to a naive weighted extension

At a fixed time, compare positive independent categorical route distributions:

- A: a=(e:1/2,h:1/2), b=(e:1/2,k:1/2), c=(e:1), d=(l:1)
- B: a=(u:1), b=(u:1/4,v:3/4), c=(u:1/2,v:1/2), d=(l:1)

Both have ordered pair same-population probabilities

    (ab,ac,ad,bc,bd,cd)=(1/4,1/2,0,1/2,0,0).

A has no ab|cd witness: a,b share only e and c is forced there. B has one: choose b at u and c at v. Thus arbitrary unequal weights invalidate a fixed-time moment-only theorem, already at four labels and support size at most two. Exact Fraction controls assert this.

This is **not** a matched full-calendar-law source pair or a G5 Q lower bound. A first chronological realization tried to place a,b's private alternatives on three ordinary rootward branches. Resolving those branches with strict positive binary intervals creates extra pair meeting atoms that the proposed alternative cannot match. Allowing a zero-duration multifurcation or silently dropping a positive-rate edge would evade the source contract. The weighted earlier 1/3–2/3 census is not eliminated by the present theorem. Whether entire calendar chronology rules out all such weighted ambiguities remains open.

## 7. Prior-art check and exact remaining full target

Before deriving the new criterion I reread Zhu–Degnan's primary NMSC discussion of parental trees and branch-length distinguishability: https://pmc.ncbi.nlm.nih.gov/articles/PMC5837799/ . The mixture method and terminal one-descendant parental-tree interpretation are established machinery. Their Pardi–Scornavacca example has equal displayed trees, so it supplies no Q-different pair-law lower bound here.

The primary MUL-tree conflict-free quartet paper, https://pmc.ncbi.nlm.nih.gov/articles/PMC3716922/ , uses a different target (conflict-free quartets resolved without contradictory occurrence selections), not the union over all positive terminal choices. Average-distance identifiability, https://doi.org/10.1007/s00285-022-01847-8 , uses an averaged scalar distance, not the six entire pair meeting CDFs. The existing G5 frozen-germ and displayed-edge bridge are source-specific accepted inputs; the new claim is the equiprobable two-position quartet criterion and its terminal-source assembly. This bounded comparison is not an exhaustive priority certificate.

The forward/version gate in `lipics-2020-2026-audit/wabi2026-forward-audit/WABI-FORWARD-GATE.md` was retained. No unreviewed NetCS/BROOQS, postconference spectral claim, software update, or independent followup was used as a mathematical input.

The unrestricted full G5 target is still: prove M2→Q over all admitted binary positive temporal cut-child sources, or give two such sources with equal every complete pair calendar law and different Q. The new theorem says a counterexample cannot have both sources in the direct-terminal/equiprobable subclass, even with differing positive edge rates and clocks. Nonuniform weights or nonterminal source operations may be needed; the local weighted obstruction makes the former a concrete next avenue, without demonstrating full-law compatibility.
