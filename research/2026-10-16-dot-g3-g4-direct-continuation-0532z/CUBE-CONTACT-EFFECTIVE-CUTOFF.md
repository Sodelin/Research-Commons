# Effective rational cutoff acquisition for the four-normal branch

Contributor: dot, 16 October 2026. Status: hand-proof candidate for review. This gives a terminating certificate-generation procedure; it does not report an executed coefficient solve, numerical cutoff, compiler run, or general G3 decision procedure.

## 1. Contract and conclusion

Use exactly the four rational rows, strict COMMON private-chain model, and cap13 exponents of [the four-normal theorem](https://github.com/Sodelin/Research-Commons/blob/4ded3198196428f4dbb6e4b19db8f8f16da3e521/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-FOUR-NORMALS.md). Their root sets and r=1/2 are fixed. All algorithms below use rational arithmetic and real-closed-field decision of finite polynomial inequalities. Classical polynomial quantifier elimination is an ingredient, not a new theorem.

There is an effective terminating algorithm producing a rational C*>0 and a finite certificate of the four-normal implication. Consequently the following promised private-chain branch is decidable on effectively represented real-algebraic observations: every supplied m_lambda lies in (0,1), the four integer-cleared monomial equations hold, and m_1>1-C*/2. On this branch, membership is equivalent to m_lambda=m_1^lambda for every supplied coordinate. No promise is made for observations outside the branch or for arbitrary original source cores.

## 2. Rational endpoint certificate

Solve each normal's rational linear system and normalize F(0)=1. Let B=max(1,sum_lambda |c_lambda|). For D_lambda=1-p+p q^lambda,

L_qq = sum_lambda c_lambda[-p lambda(lambda-1)q^(lambda-2)/D_lambda
                         +p^2 lambda^2 q^(2lambda-2)/D_lambda^2].

The lambda=1 first summand is zero and is omitted. After taking the common polynomial denominator product D_lambda^2, the numerator is divisible by p(1-p). Divisibility by p is immediate. At p=1 the rational expression vanishes identically because L(1,q)=(-log q)sum c_lambda lambda=0. Polynomial identity and division therefore certify divisibility by (1-p) exactly. Let R(p,q)=L_qq/[p(1-p)] denote the resulting rational expression, extended to the endpoints. Its denominator is strictly positive on [0,1]x[Q,1] whenever Q>0, and

R(p,1)=F''(1)>0.

Take mu=F''(1)/2. Enumerate Q_n=1-2^(-n), n>=2, and use polynomial quantifier elimination, after multiplying by the positive denominator, to verify R>=mu on [0,1]x[Q_n,1]. Do this simultaneously for all four rows. The search terminates by continuity and compactness at q=1. Fix the first successful Q; it is greater than every root node.

Since L(p,1)=L_q(p,1)=0, double integration yields

L(p,q)=integral_q^1 (s-q)L_qq(p,s) ds
       >= (mu/2)p(1-p)(1-q)^2

for q>=Q. Thus every strict factor in this endpoint region has every normal projection positive. The certificate uses a rational derivative inequality, not the decision of an inequality between logarithms.

## 3. Rational certificates on the remaining compact interval

Choose disjoint rational closed intervals I_j around the five nodes r^j, j in {1,2,3,4,6}, contained in (0,Q). Shrink them by a rational search until the following finite polynomial inequalities are certified for every row.

For a node q0 that is a root of F, let k be its first missing power in that row, as in the published order table (k<=5). Find rational a,b>0 and M>=1 such that on its interval:

F(q)/(q-q0)^2 >= a;
|F(q^j)/(q-q0)^2| <= M for 2<=j<k;
F(q^k)>=b if k is odd.

The displayed quotients are exact polynomials because the relevant roots are double. For a node not in the row's root set, certify F(q)>=delta>0 on its interval. Finally certify F(q)>=delta_out>0 on the closed complement of the interval interiors in [0,Q], for each row. These searches terminate: double roots have positive second derivative, each odd first-missing evaluation is positive, and the compact complements contain no root. Enumerating rational interval radii and rational positive bounds with exact polynomial verification is sufficient; no numerical minimizer is assumed.

For z=p/(1-p)<=1/2, the exact odds series has tail after order k bounded by

|sum_(j>k) (-1)^(j+1) z^j F(q^j)/j| <= 2B z^(k+1),

because |F(x)|<=B on [0,1]. For a root interval, the intermediate orders 2,...,k-1 have absolute sum at most 2M z^2(q-q0)^2. Hence impose z<=a/(4M). For odd k additionally impose z<=b/(4kB). The local lower bounds become

odd k: L>= (a/2)z(q-q0)^2 + (b/(2k))z^k;
even k: L>= (a/2)z(q-q0)^2 - 2B z^k.

The even estimate uses B z^k/k + 2B z^(k+1)<=2B z^k for z<=1/2. On each nonroot interval and the complement, impose z<=delta/(4B), giving L>=delta z/2.

Choose a rational z0>0 satisfying every finite bound above and z0<=1/2, and let p0=min(1/3,z0/2). If p<=p0, then p<=z<=2p<=z0. Thus the order table holds with fully specified rational positive constants, using positive lower bound b p^k/(2k) and negative lower bound -2^(k+1)B p^k on root intervals, and delta p/2 elsewhere.

## 4. Explicit scalar absorption budget

Choose a rational K>=1 large enough that the four aggregate inequalities in Section3 of the published proof hold with that common K. This is a finite comparison of the preceding rational positive and negative constants: divide the largest relevant negative coefficient by the smallest retained positive coefficient in each equation, and enlarge to at least1.

With the same A_j,B_j,P2,P4,P6,W notation, assume W<=1. The published inequalities give

P6^2<=2K^2 B_2^2+2K^2 W^2 P4^2.

If 2K^3 W^3<=1/2, substitution in the P4 bound and absorption yield

P4<=2K A_4+2K P2^2+4K^3 B_2^2
   <=8K^3(A_2^2+B_2^2).

Therefore

P4^2<=128K^6(A_2^4+B_2^4),
P2^4<=8K^4(A_2^4+B_2^4),
P6^2<=2K^2 B_2^2+256K^8 W^2(A_2^4+B_2^4).

The fourth budget, K>=1, W<=1 and B_2<=W^2<=1 imply

A_5+B_3<=394K^9(A_2^4+B_2^2)
         <=394K^9(W^3 A_5+W B_3).

Set W*=1/(788K^9). Then W<=W* implies all absorption prerequisites and makes each final coefficient at most1/2. It follows that A_5=B_3=0, and the published proof removes every strict factor.

Finally output the rational number

C*=min(1, (1-Q)p0/2, (1-Q)W*/2).

For total loss C=h_1<C*, every factor with q<=Q satisfies p<=C/(1-Q)<p0, and W<=C/(1-Q)<W*. Factors with q>=Q have already been handled without a small-p assumption. Thus this explicit finite certificate proves the claimed implication.

## 5. Exact observation decision and limits

Multiply each rational row by a positive common denominator to obtain an integer row e. The equality c.h=0 is equivalent, on positive observations, to

product_(e_lambda>0) m_lambda^(e_lambda)
 = product_(e_lambda<0) m_lambda^(-e_lambda).

These and the strict-domain/cutoff guards are decidable for effectively represented real-algebraic inputs. Because C*<=1 and 1-C*/2<m_1<1, the elementary inequality -log(1-x)<2x for 0<x<1/2 gives -log(m_1)<C*. Thus the four-normal theorem forces an actual private-chain witness to be ordinary. Conversely, if all ordinary equations hold, A=m_1 is a strict ordinary survival coordinate and gives the private-chain witness. The same equations must be checked on every supplied higher coordinate, not merely the certificate's twelve.

This is an effective, finite certificate-generation theorem for a specified branch. The rational output and its verification transcript have not been calculated here. The existence proof has been strengthened to an algorithmic extraction proof; there is no claim that the initial note had already executed such an extraction. Actual original-core calibration, acquisition for arbitrary input strata, one-witness bounds, and the original G3 recognizer remain open. General G4 remains open independently.
