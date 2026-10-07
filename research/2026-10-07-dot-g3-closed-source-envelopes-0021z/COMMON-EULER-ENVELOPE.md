# A polynomial Euler envelope for COMMON source closure

Contributor: dot (OpenAI), 6 October 2026. Separate hand candidate for independent review. This uses the older COMMON generator compression and positive reconstruction, not the INDEPENDENT weak-factor inequality. The new proposed step is an all-state semialgebraic inductive error ledger. No QE or numerical execution occurred.

## 1. Literal COMMON module and finite operator norm

Fix finite cap m>=2 and C_m=binom(m,2). Use the full labelled-forest kernel carrier from the companion INDEPENDENT envelope proof, with 0<b(K)<1 and deterministic arities zero and one. The source mode here is COMMON. A fixed unranked forest is routed as one current-root collection. The ordinary operator is E(z), and normalized physical append families are

    C(s,p,q)=E(s)[I+p(E(q)-I)], 0<s,p,q<1,
    V(s)=E(s), 0<s<1.                                    (1)

The normalization is the accepted COMMON source normalization: strip off the shorter-arm deterministic baseline and retain the ratio q. Equal arms give the separate ordinary case. Conversely, every finite product in (1), preceded by E(z) with 0<z<1, has a strict positive physical bigon/connector realization by splitting its positive deterministic baseline among all arms and connectors. The normalization does not introduce a zero-length physical arm.

For the estimates, realize a kernel as its chronological transition matrix on all finite labelled forest states at cap m: graft the relevant current-root kernel into each entering state. This matrix is row-stochastic on the entire auxiliary simplex carrier. Its row-total-variation distance agrees with the maximum of the entering-arity kernel distances, since rows are deterministic graftings and singleton input states recover the kernel coordinates. Matrix multiplication implements chronological graft composition. Thus the maximum absolute row-sum norm satisfies

    ||T_K-T_W||_infinity=2 d(K,W),
    ||T_K||_infinity=1 for stochastic K,

and supplies the carrier-wide contraction facts. No left-regular/current-root representation is interchanged. Below E, G and I denote these current-root transition matrices.

All E(q) are functions of the same finite ordinary Kingman generator and commute. They have rational polynomial entries in q. Since E(1)=I, the matrix

    D(q)=(E(q)-I)/(1-q)                                  (2)

has polynomial entries, including a polynomial continuation to q=1. Only strict 0<q<1 is needed in the finite atom representation below. It is a Markov generator: off-diagonal entries are nonnegative and each row sums to zero. An entering k-root state has no-merger probability q^binom(k,2), giving exit rate at most C_m after division by 1-q. Hence

    ||D(q)||_infinity<=2C_m.                             (3)

These COMMON generator facts and positive Poisson/Bernoulli reconstruction are prior G6 content, Section 3.4 of the immutable independent source-critical review, SHA256 58d346f1a5b21ad4229333dc3ca82b67a5ae397eb8f6e3b8bff57cd788763b48, preserved in providers/G6-INDEPENDENT-REVIEW.md. The explicit construction here builds on those statements; no new compression theorem is claimed.

## 2. Fixed finite auxiliary representation

Choose rational 0<b0<1 and 0<delta<1. Set H=1/b0-1 and N=ceil(H/delta). Choose an integer L>=max(2,ceil(C_m H)). Define

    R=C_m^2 (2H/L+delta).

Let X be a retained normalized word

    X=E(z) product_(i=1)^n [I+p_i(E(q_i)-I)],
    0<z,p_i,q_i<1, 0<=n<=N,
    d_i=p_i(1-q_i)>delta.

Commutation permits this retained COMMON product; no INDEPENDENT operator is reordered. Its positive baseline z ensures X is an actual positive source word after the usual baseline splitting.

Let r be the number of entries in the finite matrix carrier, and allow at most r+1 atoms

    G=sum_j nu_j D(u_j),  M=sum_j nu_j,
    nu_j>=0, 0<u_j<1.

Zero weights are allowed. Padding with zero weights and a fixed strict node handles fewer atoms. The augmented vectors (D(u),1) lie in a finite real vector space of dimension at most r+1. Any finite positive sum has a representation with at most r+1 terms preserving BOTH G and M: a linear dependence among more terms has coefficients of both signs because its last-coordinate sum is zero; moving along that dependence until a weight vanishes eliminates one term. In particular, adding one new strict atom to an existing representation can always be compressed back without changing G or M and without creating endpoint nodes.

For a real B>=0 impose

    n delta + M <= B,       b(K)(1+B)<=1.                (4)

In the high-pair region b(K)>=b0, this implies M<=B<=H. Hence

    A(G)=I+G/L

is row-stochastic: its maximum exit rate is at most C_m M/L<=1. The same is true along any positive atom-addition segment whose final mass is at most H. Define the POLYNOMIAL stochastic proxy

    W=X A(G)^L.                                         (5)

The proxy W is not asserted to be an actual source. Its distinction from the actual X and the closure kernel X exp(G) is essential.

## 3. Semialgebraic envelope and its initialization

For K in the auxiliary carrier define

    I_(b0,delta,L) = {b(K)<b0}
      union {b(K)>=b0 and there exist n,X,G,M,B as above
                           with (4) and d(K,W)<=R B}.    (6)

All displayed constraints are semialgebraic over Q. Matrix powers have the fixed integer exponent L. The normalized source and D(u) entries are polynomial. The integer n is a finite disjunction, and the atom count is fixed. TV inequalities are finite absolute-value inequalities and therefore semialgebraic. Formula (6) is an explicit finite existential formula, not an implemented QE computation.

Every initialization E(z) lies in (6): in the high-pair region use n=0, X=E(z), G=0, M=B=0, W=X. The low-pair region is absorbing under every physical append.

## 4. One-step Euler mismatch

Suppose G has mass M and add a weak atom d D(q), where 0<d<=delta and M+d<=H. The matrices G and D(q) commute, as both are finite linear combinations of functions of the ordinary generator. Put

    F(v)=(I+(G+v d D(q))/L)^L, 0<=v<=1.

Every base matrix in this interval is stochastic. Commuting differentiation gives

    F'(0)=d A(G)^(L-1) D(q),
    F''(v)=d^2 (L-1)/L
               (I+(G+v d D(q))/L)^(L-2) D(q)^2.

Using (3), ||G||_infinity<=2C_m H, and stochastic contraction,

    || A(G)^L d D(q)-F'(0) ||_infinity
       = || d A(G)^(L-1) G D(q)/L ||_infinity
       <=4 C_m^2 H d/L,
    ||F''(v)||_infinity<=4 C_m^2 d^2.

Taylor's integral remainder then gives

    (1/2)||A(G)^L[I+dD(q)]-A(G+dD(q))^L||_infinity
       <=2 C_m^2 H d/L + C_m^2 d^2
       <=R d.                                           (7)

The factor one half converts the row norm to TV for these stochastic kernels. This is a uniform all-auxiliary estimate on the represented generators. It does not require G to have arisen from a history of actual weak cells.

## 5. Every auxiliary witness survives every append

Take ANY witness of the high-pair part of (6), even if K is not actual. If an update crosses below b0, the first region handles it. Otherwise let c be its pair survival, d_tot=1-c and K'=K*C. Set B'=B+d_tot. Exactly as for the companion budget,

    b(K')(1+B')
      =b(K)[1+B-B d_tot-d_tot^2]<=1,

so B'<=H before further conclusions are drawn.

For a normalized cell (1), write d=p(1-q). Its pair survival is c=s(1-d), hence d_tot>=d. For an ordinary append put d=0.

**Ordinary append.** Replace z by zs, leaving n,G,M unchanged. The proxy is W'=W E(s), so contraction preserves the error bound with B' in place of B. Constraint (4) remains true.

**Strong cell, d>delta.** Replace z by zs and retain the new Bernoulli factor, increasing n by one. Keep G and M. Because all proxy factors are COMMON functions of the same generator, W'=W*C exactly. Also

    (n+1)delta+M <=B+d_tot=B'.

This implies n+1<=H/delta<=N, so the finite count does not fail in the high-pair region. No update is suppressed by a count guard. Contraction gives the required error bound.

**Weak cell, d<=delta.** Replace z by zs and G by G'=G+dD(q), with M'=M+d. Compress its augmented atom list as in Section 2, preserving G' and M'. Then

    n delta+M'<=B+d_tot=B'.

In particular the entire generator segment has mass at most H, as required by (7). The old proxy multiplied by the actual cell differs from the new proxy by at most R d: commute only the COMMON factors to write that difference as X E(s) times the bracket in (7), and use stochastic left contraction. Consequently

    d(K',W')<=d(K*C,W*C)+d(W*C,W')
             <=R B+R d<=R B'.

Thus every auxiliary witness has an updated witness for every allowed append. This proves inductiveness of the projection (6), including zero atom weights, the weak/strong threshold and crossing into the absorbing low-pair region.

## 6. Uniform distance to the actual source closure

For every represented G, exp(vG) is stochastic for v>=0. Taylor's integral remainder gives

    ||exp(G/L)-I-G/L||_infinity
       <=||G||_infinity^2/(2L^2).

Telescoping the L powers of the two stochastic matrices exp(G/L) and A(G) yields

    (1/2)||exp(G)-A(G)^L||_infinity
       <=||G||_infinity^2/(4L)
       <=C_m^2 M^2/L.                                   (8)

Now X exp(G) belongs to the closure of ACTUAL strict positive COMMON words. For each positive atom weight nu_j, take integers k_j tending to infinity with k_j>nu_j/(1-u_j). Then

    [I+(nu_j/[k_j(1-u_j)])(E(u_j)-I)]^k_j
       tends to exp(nu_j D(u_j)).

Every displayed Bernoulli probability is strictly between zero and one. Omit zero weights. Multiplying these finitely many blocks with X, and splitting its fixed positive baseline z among all finite factors, gives genuine positive source words with the same original one-slot interface. Commutation identifies their limit as X exp(G). This is a source-derived closure statement; neither A(G) nor an arbitrary convex combination is relabelled as a source.

Combining (6) and (8), every high-pair member satisfies

    dist(K,cl(S_common))
       <=R H+C_m^2 H^2/L
       =C_m^2[delta H+3H^2/L].                           (9)

For fixed b0 this bound tends effectively to zero by taking rational delta to zero and integer L to infinity, with the stated lower bound on L. It is uniform in all auxiliary witnesses and all word lengths.

## 7. Exact certificate-class consequence and limitations

Every K with 0<b(K)<1 outside cl(S_common) has positive distance to that closed set. Choose rational b0<b(K), then delta and L making (9) smaller than that distance. The finite semialgebraic inductive set (6) excludes K. Taking its relative carrier closure also excludes K when the inequality is strict: near K the pair coordinate remains greater than b0, so the distance bound passes to limits. Relative closure preserves inductiveness under each continuous physical append.

Therefore, conditional on this proof's independent acceptance, the intersection of all RELATIVELY CLOSED semialgebraic COMMON invariants is exactly cl(S_common) intersect C, just as for the separately proved INDEPENDENT envelope. The same closed canonical hierarchy and compact whole-target argument from CLOSED-HULL-COROLLARY.md apply within the COMMON mode. They never replace one mode's cell updates by the other's.

This result does not say that the unrestricted, potentially nonclosed certificate hull equals the source closure. Indeed the accepted rational-residue certificates exclude known COMMON nonattainment points inside that closure. It does not decide membership at such a boundary or prove that all remaining negative fibres have some nonclosed certificate. Noncompact fibres and positive-dimensional closure contact remain separate obligations.

The G6 generator approximation and Caratheodory reduction are prior work, as are elementary stochastic contraction and finite matrix Euler estimates. The proposed new synthesis is the finite polynomial proxy plus inductive pair-budget ledger, supplying exact membership in the semialgebraic certificate class. No original G3 recognizer, source-size bound, new nonattainment family, historical priority claim or execution result follows.
