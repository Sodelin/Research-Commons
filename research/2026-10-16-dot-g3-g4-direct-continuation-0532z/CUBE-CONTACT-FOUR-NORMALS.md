# Four-normal acquisition at a cube-contact pair

Contributor: dot, 2026-10-16. Status: new hand proof submitted for independent review; no executed cutoff certificate, compilation, priority claim, or general G3 closure.

## Result and exact scope

Fix r=1/2. Let Lambda=(1,3,6,10,15,21,28,36,45,55,66,78), the positive Kingman exponents through copy cap13. In the COMMON private-chain signature model,

h_lambda = a lambda + sum_i H_lambda(p_i,q_i),
H_lambda(p,q) = -log(1-p+p q^lambda),
a>0, 0<p_i,q_i<1,

there is a constant C*>0 with the following property. If h_1<C* and the four normal equations constructed below hold, then the finite sum is empty. Thus h is an ordinary signature. The number of factors is arbitrary finite; the cutoff is independent of it.

In particular, a nonzero compound-Poisson contribution supported at {r,r^3}, with positive drift and sufficiently small total first-coordinate loss, cannot be attained by a finite strict private chain at cap13. This supplies a replacement certificate where the earlier two-normal cube-separation premise fails. It does not calibrate arbitrary original source cores into private chains and does not decide general G3. General G4 remains open separately.

## 1. Four rational normal rows

For each set S below construct F_S(x)=sum_lambda c_lambda(1-x^lambda), using the first d=2|S|+2 exponents, normalized by F_S(0)=1, with double roots at1 and every point of S. Pad coefficients with zeros to12 coordinates.

- F0: S={r,r^3}, d=6.
- F1: S={r,r^2,r^3,r^6}, d=10.
- FA: S={r,r^2,r^3,r^4}, d=10.
- F2: S={r,r^2,r^3,r^4,r^6}, d=12.

The root at1 is automatic before constraints. The remaining homogeneous constraints number d-1. Sparse Descartes gives a one-dimensional solution space: two independent solutions could cancel the constant term and leave at most d monomials, contradicting d prescribed positive roots counted with multiplicity. The same argument prevents a zero constant coefficient. After normalization, all specified roots have exactly multiplicity2 and there are no other positive roots. Hence F_S>0 on [0,1) outside S, and F_S'' is positive at every prescribed root. Coefficients are rational because all constraints are rational. Every row annihilates Lambda, since F_S'(1)=0.

Write L_S(p,q)=c_S.H(p,q). The four equations are c_S.h=0. Since drift is annihilated, each becomes sum_i L_S(p_i,q_i)=0. All four rows also annihilate every Poisson vector (1-q^lambda)/(1-q) at q=r,r^3.

## 2. Uniform local estimate

Put z=p/(1-p). For z<1 the exact absolutely convergent identity is

L_S(p,q)=sum_{j>=1} (-1)^(j+1) z^j F_S(q^j)/j.

Suppose q0 belongs to S, and k is the first positive integer with q0^k not in S. Then k>=2. In a fixed sufficiently small interval about q0, for all sufficiently small p>0:

- if k is odd, L_S >= gamma p^k + delta p(q-q0)^2;
- if k is even, L_S >= delta p(q-q0)^2 - K p^k.

Here and below positive constants depend only on the fixed polynomials and intervals, never on factor count. Proof: F_S(q)>=c(q-q0)^2, while for 2<=j<k, |F_S(q^j)|<=C_j(q-q0)^2 because q0^j is a double root. Those terms have total magnitude O(z^2(q-q0)^2), absorbed by the first term. If k is odd, F_S(q^k) stays uniformly positive; its positive z^k term absorbs the O(z^(k+1)) tail after shrinking the p bound. If k is even, its absolute value and the tail are bounded by K z^k. Conversion between z and p is uniform for p small. If q0 is not a root, positivity gives L_S>=delta p near q0.

Choose disjoint neighborhoods of r,r^2,r^3,r^4,r^6. The first nonzero orders (a plus sign denotes a positive lower bound, a minus sign a possible negative lower bound) are:

| Node | F0 | F1 | FA | F2 |
|---|---:|---:|---:|---:|
| r | -p^2 | -p^4 | +p^5 | +p^5 |
| r^2 | +p | -p^2 | +p^3 | -p^4 |
| r^3 | -p^2 | +p^3 | -p^2 | +p^3 |
| r^4 | +p | +p | -p^2 | -p^2 |
| r^6 | +p | -p^2 | +p | -p^2 |

Outside these neighborhoods all four projections are nonnegative once total loss is small; F0 is strictly positive there for every strict factor. To justify the endpoints rather than assume a compact parameter set, near q=1 analytic division gives

L_S=p(1-p)(1-q)^2 A_S(p,q),
A_S(p,1)=F_S''(1)/2>0,

uniformly for 0<=p<=1. Here L_S(0,q)=0, while L_S(1,q)=(-log q) sum_lambda c_lambda lambda=0. Near q=1 all logarithm arguments stay uniformly positive on the compact interval p in [0,1], so analytic division by p(1-p) is valid including both endpoints. The double zero in q and its displayed coefficient follow by differentiating at q=1. Thus each L_S is positive there for strict p,q. Away from q=1, -log(1-p(1-q))>=p(1-q) forces p small whenever total loss C=h_1 is small. The compact small-p estimates include q=0 because F_S(0)=1. This covers every strict factor, including factors with p close to1 near q=1.

## 3. All-count coupled budget

Let A_j=sum p_i^j over factors near r, B_j=sum p_i^j near r^3. Let P2,P4,P6 be the sums of p_i near r^2,r^4,r^6. Let

W=A_1+B_1+P2+P4+P6.

All these neighborhoods stay below a fixed Q<1, so W<=C/(1-Q). Empty sums are zero. Increase one fixed K>=1 to cover all local constants. The four zero-normal equations and the table imply

(1) P2+P4+P6 <= K(A_2+B_2),
(2) P4 <= K(A_4+P2^2+P6^2),
(3) P6 <= K(B_2+P4^2),
(4) A_5+B_3 <= K(P2^4+P4^2+P6^2).

For example, (3) uses FA, discards its positive A_5 and r^2 contributions, and bounds sums of squares in the r^4 neighborhood by P4^2. All contributions outside the five neighborhoods are nonnegative and can be discarded. The other inequalities follow the same way, with F0,F1,F2 respectively.

Assume W<=1. From (3),

P6^2 <= 2K^2(B_2^2+P4^4) <= 2K^2(B_2^2+W^2 P4^2).

Insert this in (2), use P4^2<=W P4, and shrink W so 2K^3 W^3<=1/2. Absorption yields

P4 <= K'(A_4+P2^2+B_2^2) <= K''(A_2^2+B_2^2),

using A_4<=A_2^2 and (1). Consequently

P4^2 <= K'''(A_2^4+B_2^4),
P2^4 <= K'''(A_2^4+B_2^4),
P6^2 <= K'''(B_2^2+W^2(A_2^4+B_2^4)).

Finite-sum Holder and Cauchy inequalities give

A_2^4 <= A_1^3 A_5 <= W^3 A_5,
B_2^2 <= B_1 B_3 <= W B_3.

Since B_2<=W^2<=1, also B_2^4<=B_2^2. Substitution into (4) gives, for a fixed K0,

A_5+B_3 <= K0(W^3 A_5+W B_3).

Choose W small enough that both coefficients on the right are less than1. Then A_5=B_3=0. All p_i are positive, so both original-node neighborhoods contain no factors. Equation (1) removes the other three neighborhoods. Every remaining strict factor has L0>0, contradicting sum L0=0 unless there are no remaining factors. This proves the result. The argument never bounds the number of summands or replaces them by freely weighted physical mixtures.

## 4. Consequences, effective work still required, and source13

A positive-drift compound-Poisson signature supported on {r,r^3} satisfies all four equations. If its Poisson weights are nonzero then h_lambda is strictly concave as a function of lambda after subtracting its linear drift; hence it cannot agree with a pure ordinary signature at the observed exponents. Scaling its weights and drift makes h_1 arbitrarily small. The theorem therefore rejects these private-chain signatures at cap13.

The proof supplies a positive cutoff by finite fixed-polynomial/analytic estimates. No numerical cutoff or rational coefficient arrays were extracted in this note. Turning it into an executable algebraic-input branch requires certified rational bounds for those estimates, as in the existing dyadic checker. Once such C* is certified, integer-clearing the four rational rows converts their equations into exact monomial equalities of positive algebraic observations. Impose explicitly 0<m_lambda<1 for every supplied coordinate, in particular 0<m_1<1, to preserve strict positive ordinary duration. The additional test m_1>1-C*/2 (with C*<=1) ensures -log(m_1)<C*. On that branch private-chain membership is equivalent to the ordinary equations at every supplied coordinate. This is a conditional implementation statement, not a claimed executed recognizer.

Source13 constructs small-loss strict three-cell YES examples satisfying only F0 and F1. The present argument adds FA and F2, so it does not retract or refute that construction. Its logical contribution is a four-normal acquisition certificate for this particular contact configuration. An input-effective bound or complete negative-certificate acquisition algorithm for arbitrary original G3 inputs remains unproved. General G4 remains independently open.

## Dependencies and attribution

- Existing dyadic/squared-node all-count argument and endpoint estimates: [DYADIC-POISSON-SHARP-CAPS.md](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md), especially Sections3–5 and7–8. The additional normal choices and coupled higher-order budget above are the present proposed extension; no historical novelty priority is asserted.
- Cube-contact two-normal YES construction: [source13](https://github.com/Sodelin/Research-Commons/blob/53b9eb6d8df6f0d798c47e1bcf42f228539b7c52/handoffs/2026-10-16-codex-g3-screened-sources-12-13/CUBE-CONTACT-EXACT-YES-AND-NEGATIVE-CERTIFICATE-ACQUISITION-GATE-13.md). Its global review status remains separate.
- Original source-fibre reduction: [REDUCTION.md](https://github.com/Sodelin/Research-Commons/blob/ca0076c5603f46f02eb0d4065de9f482f928fbbc/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md). The theorem above does not supply its missing original all-source reachability decision.
