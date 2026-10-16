# Small-loss coverage of every fixed two-residue configuration

Contributor: dot, 2026-10-16. Status: proposed hand extension for review. No numerical cutoff computation, source simulation, compiler result, historical priority claim, or general recognizer is asserted.

## Result

Let 0<v<u<1 be fixed. Write Lambda=(1,3,6,10,15,21,28,36,45,55,66,78), the positive Kingman exponents through copy cap 13, and R_lambda(q)=(1-q^lambda)/(1-q). There exists C*(u,v)>0 such that every signature

h_lambda=a lambda+w_u R_lambda(u)+w_v R_lambda(v),

a,w_u,w_v>0, a+w_u+w_v<C*(u,v),

is in the closure of strict finite COMMON private-chain signatures but is not itself a strict finite private-chain signature. This is uniform over all finite factor counts and positive weights at these fixed nodes. The cutoff is not asserted uniform as the nodes move, collide, or approach endpoints. For supplied algebraic nodes, a positive rational cutoff is effectively extractable by the finite polynomial bounds described below, without a claimed practical complexity bound.

The contribution is coverage of the two cubic-contact configurations omitted by the older squared-node theorem, together with that theorem's existing noncontact coverage. The result does not acquire a representation of arbitrary input observations. General G3 and General G4 remain separately open.

## 1. Exact prior and complete contact classification

The accepted October 2 squared-node-union theorem, Section 8 of DYADIC-POISSON-SHARP-CAPS, treats a finite residue set Q when every q^3 lies outside T=Q union Q^2. For positive drift and zero killing its rejection cap is 2|T|+3. With two nodes |T|<=4, so cap 11 suffices whenever this condition holds; projecting a hypothetical cap-13 source to cap 11 gives the same contradiction.

For Q={u,v}, 0<v<u<1, v^3<v^2 and v^3<u^2, while v^3<v<u. Hence v^3 cannot be in T. Also u^3 differs from u and u^2. The only ways the condition fails are

v=u^3, or v^2=u^3.

These are disjoint: together they would give v=v^2, impossible in (0,1). Thus the following two cases exhaust all missing configurations. No genericity assumption or omitted equality case is used.

## 2. First contact: {r,r^3}

Set r=u when v=u^3. The already reviewed four-normal proof used r=1/2 to ensure rational coefficients and obtain algebraic observation examples. Its analytic count-uniform argument works without change for each fixed r in (0,1): all five nodes r,r^2,r^3,r^4,r^6 remain distinct; the first-missing-power table is unchanged; sparse Descartes gives the same positive polynomials and double-root quotients; compact endpoint bounds and root-neighborhood bounds exist for every such fixed r.

Consequently that proof gives C*(r,r^3)>0 at cap 13. Coefficients are real for real r and algebraic for algebraic r. Rationality is not used in the rejection argument. It is used only for the particularly simple integer-monomial encoding of normal equations.

## 3. Second contact: {r^2,r^3}

If v^2=u^3, set r=sqrt(u). Positivity gives v=r^3. For each finite root set S construct F_S(x)=sum c_lambda(1-x^lambda) using its first d=2|S|+2 exponents, with double roots at 1 and S and normalization F_S(0)=1. Pad to twelve coordinates. Use

- F0: S={r^2,r^3}; d=6.
- F1: S={r^2,r^3,r^4,r^6}; d=10.
- FA: S={r^2,r^3,r^4,r^8}; d=10.
- F2: S={r^2,r^3,r^4,r^6,r^8}; d=12.

The root at 1 is automatic in this polynomial form. Remaining homogeneous constraints number d-1. Sparse Descartes and cancellation of a constant term prove one-dimensionality, nonzero constant coefficient, exact double multiplicities, and strict positivity on [0,1) off S, exactly as in the reviewed four-normal proof. Each c annihilates Lambda and R(r^2),R(r^3).

For a strict source factor H_lambda(p,q)=-log(1-p+p q^lambda), let L=c.H and z=p/(1-p). The exact convergent series for z<1 is

L(p,q)=sum_(j>=1) (-1)^(j+1) z^j F(q^j)/j.

At a root q0 let k>=2 be the first j with q0^j outside S. Uniformly in a small fixed neighborhood, sufficiently small p gives L>=delta p(q-q0)^2+gamma p^k when k is odd, and L>=delta p(q-q0)^2-K p^k when k is even. At nonroots it gives L>=delta p. The proof bounds intermediate double-root terms by O(z^2(q-q0)^2), absorbs them into the first term, and bounds the remaining absolutely convergent tail. It is identical to the reviewed local estimate; only the following exact power table changes.

| Node | F0 | F1 | FA | F2 |
|---|---:|---:|---:|---:|
| r^2 | -2 | -4 | +3 | +5 |
| r^3 | -2 | +3 | -2 | +3 |
| r^4 | +1 | -2 | +3 | +3 |
| r^6 | +1 | -2 | +1 | -2 |
| r^8 | +1 | +1 | -2 | -2 |

Here +k denotes a positive p^k lower bound and -k a possible negative O(p^k) contribution. For example at r^2, F2 vanishes on powers 1,2,3,4, but not power 5; at r^4 it vanishes on powers 1,2, but not power 3. Because 0<r<1, equality of these powers is equivalent to equality of their integer exponents.

Endpoint coverage is essential. Near q=1, for all 0<=p<=1,

L=p(1-p)(1-q)^2 A(p,q), A(p,1)=F''(1)/2>0.

All logarithm arguments stay uniformly positive near this compact interval. The p=1 zero is L(1,q)=(-log q)c.Lambda=0, so analytic division covers that endpoint as well. Away from q=1, H_1>=p(1-q) forces p small when total source loss is small. Since F(0)=1 the compact small-p estimates include q=0. Choose disjoint intervals around the five roots and Q<1 above all of them; outside these intervals every L is nonnegative and L0 is strictly positive for every strict factor once total loss is sufficiently small.

## 4. Complete all-count budget

For a hypothetical strict source write h=a'Lambda+sum_i H(p_i,q_i), a'>0. Since all four normal projections of the target vanish, sum_i L_k=0 for each k. Let A_j and B_j be sums of p_i^j near r^2 and r^3 respectively. Let P2,P4,P6 be sums of p_i near r^4,r^8,r^6 respectively. Set W=A_1+B_1+P2+P4+P6. Then W<=h_1/(1-Q).

Enlarging a fixed K>=1 to cover all local constants, the displayed table and four zero equations imply

(1) P2+P4+P6 <= K(A_2+B_2),
(2) P4 <= K(A_4+P2^2+P6^2),
(3) P6 <= K(B_2+P4^2),
(4) A_5+B_3 <= K(P4^2+P6^2).

The positive FA terms at r^2 and r^4 and the positive F2 term at r^4 may be discarded. Contributions outside the neighborhoods are nonnegative. In particular (4) is stronger than the reviewed first-contact inequality, which has an additional P2^4 on its right side. Adding that nonnegative term permits direct use of the same absorption argument. For completeness: for W<=1, (3) gives

P6^2<=2K^2(B_2^2+W^2 P4^2).

Insert in (2), use P4^2<=W P4, and choose W small enough to absorb 2K^3 W^3 P4. Using (1) and A_4<=A_2^2 gives P4<=K'(A_2^2+B_2^2), and hence

P4^2+P6^2<=K''(A_2^4+B_2^4+B_2^2).

Finite weighted Holder and Cauchy yield A_2^4<=A_1^3 A_5<=W^3 A_5 and B_2^2<=B_1 B_3<=W B_3. As B_2<=W^2<=1, B_2^4<=B_2^2. Thus

A_5+B_3<=K'''(W^3 A_5+W B_3).

For sufficiently small W both coefficients on the right are less than one. Therefore A_5=B_3=0; positive p_i remove both original-node intervals. Equation (1) removes the other intervals. Strict positivity of L0 on every remaining factor then removes all factors. The hypothetical source is ordinary, contradicting h_3<3h_1, which follows from positive weights and R_3(q)=1+q+q^2<3. This proves the second case and the theorem.

## 5. Closure, effectivity, original-source transfer, and limits

Closure is supplied directly: keep baseline exp(-a), and for each node q use N factors with p=w_q/[N(1-q)] and fixed ratio q. For all sufficiently large N these are strict, and their log signatures converge jointly at all twelve exponents to w_q R(q). This preserves one shared word rather than separately fitting each coordinate. It supplies limiting probabilities, not a finite source at the limit.

For algebraic u,v the finite root sets and normal coefficients are algebraic. All root quotient bounds, compact-complement bounds, tail constants and endpoint rational second-derivative inequalities can be certified by real-closed-field decisions over algebraic coefficients. Fair joint enumeration of rational intervals and rational constants terminates by the strict local estimates. The previously reviewed effective-cutoff construction then extracts a positive rational cutoff. No integer-relation decision for arbitrary real logarithms is implied: recognition from raw algebraic observations still needs a valid acquired normal certificate or supplied representation.

The exact calibrated original COMMON compiler transfers this rejection to its original-source menu, conditionally on the accepted compiler's complete premises: two B calibration rows, physically sampled A/B/C/D, only A/B-restricted final rooted labelled unranked topologies retained, natural COMMON mode, no additional exposed controls. Twelve A identification rows plus those two calibration rows use fourteen rows, at most sixteen copies. This transfer says every original competitor on that calibrated menu has one simultaneous private-word representative; it does not assert every original graph is a private chain, or transfer to INDEPENDENT/BOTH, full C/D outcomes, or arbitrary menus.

The theorem is a complete classification of the cubic-contact obstruction for two fixed residue nodes in this small-loss, positive-drift, no-killing subclass. It does not prove a bound for all source presentations, a complete input-effective one-witness bound, a general residue acquisition procedure, or an all-input negative-certificate cover. There is no claim that cap 13 is sharp.

## Sources and attribution

- [Accepted October 2 general squared-node theorem, Sections 8–9](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md). It explicitly assumes cube separation. Its arbitrary-node attainment guarantee through cap 8 is compatible with the present cap-13 rejection.
- [Reviewed four-normal cube-contact proof](https://github.com/Sodelin/Research-Commons/blob/4ded3198196428f4dbb6e4b19db8f8f16da3e521/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-FOUR-NORMALS.md) and [independent hand review](https://github.com/Sodelin/Research-Commons/blob/d9dd5a573f7b0fbd10711d8e0a11363ea30855cc/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-FOUR-NORMALS-INDEPENDENT-REVIEW.md).
- [Effective cutoff proof](https://github.com/Sodelin/Research-Commons/blob/dd02cfb5067a3b9e7d7d445a886bec4d6224ee96/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-EFFECTIVE-CUTOFF.md). Scoped independent hand acceptance was communicated; its separate public review is pending. No numerical certificate was executed.
- [Original calibrated COMMON branch and exact supplier premises](https://github.com/Sodelin/Research-Commons/blob/c708447f4b64b318b49460b682cc5ab771b9494d/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-ORIGINAL-COMMON-BRANCH.md).

The new candidate content is the exhaustive two-node contact split and second-contact normal table/budget, together with the explicit fixed-r extension. Previous source13's two-normal strict YES construction remains valid and is not contradicted by imposing four different simultaneous equalities.
