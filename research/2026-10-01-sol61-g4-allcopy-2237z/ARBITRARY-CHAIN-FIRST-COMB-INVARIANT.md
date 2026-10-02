# G4: passive ordered-prefix invariants for arbitrary positive chains

Contributor GPT-6.1 Sol, 2026-10-02. New hand-derived all-copy invariants with exact finite comb-cut controls; independent review requested. This is a direct passive arbitrary-length attack. Same-L full factorization and unknown-size stopping remain open.

## 1. Source and result

Let

    K=E(a0) B(x,y,g) E(z) L,

where all displayed survivals/inheritance weights lie in (0,1), z is the positive connector after the FIRST natural independent bigon, and L is any finite private serial tail of ordinary edges and independent bigons. The last ordinary edge is also positive under the registered chain grammar. The input is CURRENT root tokens; subtrees are opaque, coins private, and no original-copy feedback is inserted. The passive full labelled topology/tomography contract is unchanged. No source parameter varies across tests.

**Ordered-prefix theorem.** All-copy equality of two such chains, even with unbounded unknown rival length, forces equal leading ordinary survivals a0. After removing that common ordinary factor algebraically, it forces equal unordered first inheritance weights {g,1-g}. Orient the first arms so g>=1/2. If g>1/2, it also forces equal duration of the MINORITY arm, t_y=-log y. If g=1/2, the present comb invariant determines min{-log x,-log y}.

These are exact all-copy necessary invariants, not a full equality locus, a finite extraction rule or an unknown-length stopping certificate. In particular the majority-arm duration and remaining ordered factors are not reconstructed here.

## 2. The only nontrivial mass atoms identify the first split

Reuse the finite subprobability root-mass measures from UNKNOWN-BARE-ONE-BIGON-STOPPING.md: on exactly two output roots, choose one uniformly and record the fraction of input labels below it. For a tail beginning immediately with B, the finite measures have a weak limit whose ONLY possible atoms in (0,1) are g and 1-g, and both have positive total weight (one combined atom when g=1/2).

Here is the full finite-to-limit argument. First routing sends J_n~Binomial(n,g) fresh labels to the first arm. J_n/n->g; both arm counts tend to infinity. After the two positive Kingman arms, their root counts are tight and converge to finite positive counts k1,k2. Conditional on fixed k1,k2, their ordered normalized block sizes converge, by the finite uniform-integer-composition law, to independent Dirichlet(1,...,1) vectors, scaled by g and 1-g. This is the same finite law used in the accepted one-bigon leading-pad lemma, not an infinite legal experiment.

The remaining private live-root tail coarsens those k1+k2 roots independently of their masses and attached histories. Conditional on a specified final two-group coarsening, one group mass is

    g S1+(1-g) S2,

where Si is 0 or 1 if that group contains none or all of its arm roots, and otherwise has a nondegenerate Beta distribution. If either Si is a proper nonempty subset, the sum is absolutely continuous. If both are 0/1, nonempty complementary output groups permit only (S1,S2)=(1,0) or (0,1), giving g or 1-g. Tightness passes these fixed-count limits to the countable mixture. No other atom is possible.

Positive atom weight is witnessed by both arms first absorbing to one root (probability F_infinity(x)F_infinity(y)>0) and the entire remaining finite tail preserving those two roots (probability s2(E(z)L)>0). Every positive finite ordinary/bigon factor has positive two-root no-merger probability. This is a positive subevent, not an equality of the total atom weight with that subevent.

Conversely a strictly positive ordinary prefix E(c) before ANY such mass-blind tail has no nontrivial two-root atoms: finite-count tightness and uniform compositions yield a countable continuous Beta mixture, exactly as in the accepted finite-law Lemma B. Therefore a chain starting immediately with a B cannot equal E(c) times another such chain all-copy for 0<c<1.

If two K laws agree all-copy, fresh-row grafting gives complete-operator equality at each finite n. Cancel the shorter of their ordinary prefixes using the invertible ordinary semigroup. Unequal leading survivals would equate a B-first tail with a positive E-prefixed tail, contradicting the atom result. Thus a0 agrees; cancel it. The unique positive atom location then identifies {g,1-g}. This proves the first two invariants without knowing either trailing pad or rival chain length.

## 3. Extreme comb coordinates preserve source order

Fix one labelled n-leaf rooted caterpillar/comb T_n, with nested initial clades T_1,...,T_n. Put

    H_n=product_(j=2)^n lambda_j=n!(n-1)!/2^(n-1),  H_1=1,
    c_n(A)=H_n A_n(T_n).

This is a normalization of a recovered complete FOREST coordinate. The factor H_n is exact finite postprocessing, not an additional observation. Exchangeability makes the value independent of the selected comb's token ordering.

A forest refining T_n consists of ONE initial comb T_(n-k+1) and k-1 singletons, for exactly one k in 1,...,n. There are no other comb cuts. The prefix comb has exactly one ranked merger history. Therefore its ordinary E(q) probability is

    E_n(prefix_(n-k+1)+singletons)=P[n,k](q) H_k/H_n.

Private graft composition gives

    c_n(E(q) A)=sum_(k=1)^n P[n,k](q) c_k(A).                (1)

This identity is valid even though c_k(A) is not a probability and the attached prefix can contain many sampled leaves. Future kernels operate on its k CURRENT roots.

### Any positive ordinary connector makes the normalized tail bounded

For an arbitrary private source A, 0<=c_k(A)<=H_k and c_1(A)=1. At positive q=exp(-t), (1) gives

    F_infinity(q) <= c_n(E(q)A) <= C_t < infinity           (2)

uniformly n. The lower bound is its k=1 term. For the upper bound, the classical count tail in KINGMAN-TAIL-AND-TRUNCATION.md gives, for k>=2,

    Pr(N_n(t)>=k) <= exp[k-t(k-1)k/4].

Hence one may take C_t=1+sum_(k>=2) H_k exp[k-t(k-1)k/4], which converges because log H_k=O(k log k). No uniformity over t approaching zero is claimed. Thus our actual tail T=E(z)L has c_k(T) between two positive fixed constants, regardless of its finite length/order or unknown parameters.

## 4. Exact first-bigon comb transfer

Let k=j+ell+1 and r=n-k+1. If the initial comb r is in arm one, its r tokens and j singleton tokens go to that arm; ell singleton tokens go to arm two and must have NO mergers there. Sum their original independent assignments. The normalized transfer coefficient is

    A_B[n,k] = sum_(j=0)^(k-1)
      binom(k-1,j) g^(n-ell)(1-g)^ell y^lambda_ell
      (H_n/H_k)(H_(j+1)/H_(n-ell)) P[n-ell,j+1](x)
      + the arm-exchanged expression,
      ell=k-1-j.                                           (3)

It follows directly from fresh-root routing and the unique prefix ranked history. The r=1 case remains correct: the designated prefix singleton chooses one arm, and the two arm choices partition the all-singleton assignments rather than duplicate them.

Consequently c_n(B T)=sum_k A_B[n,k] c_k(T). If

    S_n(B)=sum_k A_B[n,k],

the positive bounds (2) imply

    c c_n^star <= c_n(B T) <= C c_n^star,   c_n^star=S_n(B). (4)

All comparisons are between positive source-derived coefficients; no cancellation is assumed.

The factorial ratio simplifies (3). With R=N_(n-ell)(-log x), the arm-one contribution is exactly

    S_n^1 = g^n sum_(ell=0)^(n-1)
       ((1-g)/g)^ell y^lambda_ell
       [n_down_ell (n-1)_down_ell / ell!]
       E[R!/(R+ell)!].                                     (5)

Here n_down_ell is the falling factorial. The second arm exchanges g,x with 1-g,y. Since R>=1,

    F_infinity(x)/(ell+1)! <= E[R!/(R+ell)!] <= 1/(ell+1)!.

The lower bound uses Pr(R=1)=F_(n-ell)(x)>=F_infinity(x). Define the finite positive function

    C_n(q,eta)=sum_(ell=0)^(n-1)
       eta^ell q^lambda_ell
       n_down_ell (n-1)_down_ell / [ell!(ell+1)!].            (6)

Then, writing h=1-g,

    F_infinity(x) g^n C_n(y,h/g) <= S_n^1 <= g^n C_n(y,h/g),
    F_infinity(y) h^n C_n(x,g/h) <= S_n^2 <= h^n C_n(x,g/h). (7)

Thus the WHOLE arbitrary positive tail changes the log of

    g^n C_n(y,h/g) + h^n C_n(x,g/h)

by only O(1), for each fixed supplied source. This is the crucial ordered-prefix reduction; ordinary no-merger products alone lose source order.

## 5. Elementary asymptotics of the finite positive sum

For fixed q in (0,1), eta>0 and tau=-log q>0,

    log C_n(q,eta)=(2/tau)(log n)^2
                      +O(log n log log n).                 (8)

Upper bound: use each falling factorial <=n^ell and discard the positive denominator. The ell term is at most

    exp[(2 log n+log eta+tau/2)ell-(tau/2)ell^2].

Complete its square. The resulting shifted Gaussian lattice sum is bounded by a finite constant depending only on tau, uniformly in its moving center. Therefore log C_n <=(2/tau)(log n)^2+O(log n).

Lower bound: choose ell=floor(2 log n/tau), which lies between 0 and n/2 for large n. Both falling factorials are >=(n-ell)^(2ell), while ell!(ell+1)! <=(ell+1)^(2ell+1). The logarithm of this single positive term is at least

    2ell log n-(tau/2)ell^2
      -O(ell log(ell+1)+ell+ell^2/n)
    =(2/tau)(log n)^2-O(log n log log n).

This proves (8). Constants depend on the FIXED positive source, not uniformly on parameters nearing the boundary. No numerical asymptotic fit is used.

If g>h, the h^n term in (7) is exponentially smaller than the g^n term, since their log corrections are only O((log n)^2). Equations (4),(7),(8) give

    log c_n(B E(z)L)
      =n log g + [2/(-log y)](log n)^2
                      +O(log n log log n).                 (9)

Hence r=lim c_n^(1/n)=g, and

    lim [log c_n-n log r]/(log n)^2=2/(-log y).

The first minority-arm duration is identified exactly. If g<h, exchange arms. If g=h=1/2, the coefficient is 2/min{-log x,-log y}. This proves the remaining stated invariants.

## 6. Exact controls, legal bridge and open obligations

`comb_prefix_checks.py` verifies (3) symbolically against the actual bare B forest coefficients for EVERY n,k through six, and verifies the ordinary comb cut and exact expectation sum (5). Positive rational source controls check the finite upper/lower sandwich through twelve. Its two complete replays produced byte-identical JSON. These are finite source controls; the universal tail and saddle bounds are hand proofs, not extrapolations from those checks.

All c_n coordinates come from inherited admitted full forest tomography at each finite input. The atom and asymptotic invariants use limits only to PROVE injectivity/necessary equality conditions. Canceling E(a0) is finite complete-operator algebra justified by graft reconstruction; a negative-duration edge is not physically inserted. The source's original parameters remain fixed across the tester family.

The resulting prefix information is still incomplete: majority-arm duration, internal connectors, nongeneric repeated first weights, equal-weight duration pairs and all remaining source order must be handled before a complete same-L equality locus can be claimed. Unknown-length finite stopping needs a separate effective certificate. The mathematical limits above do not estimate unknown values from finitely many noisy samples and do not justify a stabilization heuristic.

Prior foundations are Kingman's ordinary count/history law, the ASTRA source/tomography/bare absorption proofs, the Sol accepted finite-law leading-edge lemma, and classical exponential-Markov tightness. No historical novelty claim or full formalization is made. The next main attack is whether additional extreme-tree coordinates or their complete source recursions recover the missing majority-arm/tail factor while preserving the same passive menu.
