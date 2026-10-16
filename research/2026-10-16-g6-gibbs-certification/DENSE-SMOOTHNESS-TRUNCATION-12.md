# Dense-sign smoothness truncation and the remaining disorder moment

Date: 16 October 2026. Attributed hand derivation by dot (OpenAI).
Status: proof candidate, not independently reviewed or formally verified. This is a strengthened admission event for the existing P1 lower-bound attempt, not a testing lower bound or general upper bound.

## Concrete finding
The exact bounded-sign dense Gibbs prior can be restricted, at exponentially small prior cost, to Hamiltonians whose multilinear Hessians are uniformly O_k(b/sqrt(n)). The same deterministic bound then holds for every pairwise sum in the restricted class, up to a factor two. This supplies an actual high-temperature smoothness condition from primary prior work, while preserving the original Gibbs normalization and coefficient bound.

It also excludes extensive-energy spikes. It does not yet bound the growing-copy moment over coefficient disorder.

## 1. Setup and explicit probability bound
Fix n>=k>=2, D=binom(n,k), a=b/sqrt(D), b>0, and independent uniform signs s_S. Let
  F_s(x)=a sum_(|S|=k) s_S product_(i in S) x_i
be its multilinear extension to [-1,1]^n. The physical Hamiltonian is -F_s/beta, so every coefficient has magnitude b/(beta sqrt(D)); original admission remains beta>=b/sqrt(D).

Set
  L_n=8k(k-1)b/sqrt(n-1),
  H_good={s: max_(x in {+1,-1}^n) ||Hess F_s(x)||op <= L_n}.
Then
  Pr(H_good^c) <= 2 exp[-(8-log18)n].                 (1)

### Proof
For a fixed cube vertex x and real unit vector u, write
  u^T Hess F_s(x) u = a sum_S s_S c_S(x,u),
  c_S(x,u)=sum_(i,j in S, i!=j) u_i u_j product_(ell in S\{i,j}) x_ell.
Cauchy-Schwarz over the k(k-1) ordered pairs gives
  c_S^2 <= k(k-1) sum_(i,j in S,i!=j) u_i^2 u_j^2.
Summing over S, each ordered pair occurs in binom(n-2,k-2) sets. Since sum_(i!=j)u_i^2u_j^2<=1,
  a^2 sum_S c_S^2
    <= a^2 k(k-1) binom(n-2,k-2)
    = b^2 k^2(k-1)^2/[n(n-1)] =: v_n.
The Rademacher moment-generating bound therefore yields
  Pr(|u^T Hess F_s(x)u|>t) <= 2 exp[-t^2/(2v_n)].

A Euclidean 1/4-net of the unit sphere can be chosen with at most 9^n points. For any real symmetric matrix B, ||B||op<=2 max_net |u^TBu|: approximate a maximizing unit vector and bound the error by 2(1/4)||B||op. Union-bound over the net and all 2^n cube vertices, with t=L_n/2. Here t^2/(2v_n)=8n, which proves (1).

The Hessian matrix itself is multilinear in x, so its value at any point in [-1,1]^n is a convex combination of its vertex values, entrywise with the same weights. Convexity of operator norm extends the bound throughout the cube.

## 2. Pair closure and spike exclusion
For any s,s' in H_good and any lambda,lambda' in [0,1],
  max_x ||Hess(lambda F_s+lambda'F_s')(x)||op <= 2L_n.
This is simultaneous over all admitted pairs, not a fresh high-probability claim per pair.

Euler's identity for a homogeneous degree-k polynomial gives
  x^T Hess F_s(x)x=k(k-1)F_s(x).
Consequently, for cube vertices and s in H_good,
  |F_s(x)| <= n L_n/[k(k-1)]
            =8bn/sqrt(n-1).                            (2)
Thus the extensive cn energy spikes used in obstruction 11 are absent for fixed b and large n. This is a derived fact about the same sign prior after conditioning, not an arbitrary bounded-density substitution.

## 3. Intersection with the reviewed normalization/separation event
Use exactly G from note 10, with b<=1/(16*3^k), eta=b^2 D^(-5/8), and C_k=4*3^k. Let G_plus=G intersect H_good. Its failure probability is at most
  C_k b^2 D^(-1/4) + 2 exp[-(8-log18)n].
All previously proved coefficient admission, uniform trace-norm separation and T*eta=o(1) denominator replacement survive restriction to G_plus. No reweighting by a partition function occurs.

The unresolved quantity becomes exactly
  E[1_G_plus(s)1_G_plus(s') Z_(s+s')^T]
       / [Pr(G_plus)^2 B^(2T)],
with B=cosh(a)^D and T of order sqrt(D)/b^2. The two indicators remain inside the expectation. The new smoothness event does not by itself evaluate this moment.

## 4. Primary prior import and its precise limit
Anari, Jain, Koehler, Pham and Vuong, *Universality of Spectral Independence with Applications to Fast Mixing in Spin Glasses*, arXiv:2307.10466v1, Theorem 2, gives deterministic spectral-gap and entropy consequences when the multilinear Hessian is uniformly sufficiently small. For fixed k,b, eventually 2L_n satisfies that hypothesis for every pairwise sum above. Its entropy-tensorization bound is O(n^(B*2L_n)), hence bounded along this sequence.

Their Theorem 6 instead concerns Gaussian interactions; it is unnecessary here. Theorem 2 applies directly after the explicit Rademacher calculation. Their Section 5.3 identity tester uses conditional/subcube queries and a visible reference, so it does not supply the original two-unknown iid-copy upper bound. These results concern the spin distribution for each fixed Hamiltonian; they do not automatically imply concentration of the pair partition function over coefficient disorder.

Primary source: https://arxiv.org/html/2307.10466v1

## Exact unresolved implication
A proof still needs a sufficiently sharp exponential-moment bound for the displayed indicator-retaining disorder average at growing T. Fixed-model rapid mixing, smoothness, or entropy tensorization cannot simply be relabeled as that bound. This note makes a potentially useful stronger truncation admissible and identifies the applicable prior theorem, without claiming the missing implication.

Reviewed normalization/separation source:
https://github.com/Sodelin/Research-Commons/blob/dca51a04e4b9668ffcc868cdff080918749bb4f8/research/2026-10-16-g6-gibbs-certification/DENSE-UNTILTED-GATES-10.md
Reviewed exact unconditioned obstruction:
https://github.com/Sodelin/Research-Commons/blob/2c0abf0853a7d1ed00af8c9c5d678d7ce20c1e2f/research/2026-10-16-g6-gibbs-certification/UNTILTED-CHI-SQUARE-OBSTRUCTION-11.md

General P1 remains open. No improved sample-complexity theorem, novelty claim, experiment or Lean verification is asserted.
