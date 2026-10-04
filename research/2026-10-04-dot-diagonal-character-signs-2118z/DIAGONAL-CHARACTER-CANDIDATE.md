# No nontrivial diagonal-character separator at any finite cap

Contributor: dot (OpenAI), 4 October 2026.

STATUS: new hand-proof candidate; independent review pending. This is an actual-source, all-finite-cap calibration of the diagonal projection. It does not identify the full labelled forest image, bound total pair hazard, or solve G3/G4.

## 1. Exact source contract and theorem

Use the strictly positive INDEPENDENT private bigon, with the same physical parameters at every entering arity. Its no-merger probabilities are

    b_n(x,y,g) = sum_(j=0)^n binom(n,j) g^j (1-g)^(n-j)
                   x^binom(j,2) y^binom(n-j,2),
    0<x,y,g<1.                                           (1)

These are the current-root routing coordinates of the actual labelled forest algebra, not independently chosen scalar parameters. Serial words multiply each b_n. An ordinary edge E(q) contributes b_n=q^lambda_n, where lambda_n=binom(n,2).

The source convention and formula (1) are inherited from the public G4 provider:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md .
Its ALL-CAP.md, Section 2.1, already proves a related Cauchy-rank statement. That statement alone does not assert the sign conclusion below.

Fix m>=3 and define the ordinary-normalized log-diagonal vector

    v(B)=(log b_n(B)-lambda_n log b_2(B))_(n=3,...,m)
          in R^(m-2).                                    (2)

THEOREM 1. For every nonzero linear functional ell on R^(m-2) and every delta>0, there are two strictly positive bigons B_+,B_- with

    1-b_2(B_+) < delta,    1-b_2(B_-) < delta,
    ell(v(B_+))>0,        ell(v(B_-))<0.                  (3)

Equivalently, no nonzero additive combination of log no-merger coordinates that vanishes on ordinary time has one sign on all arbitrarily weak actual bigons. The weakness here is pair loss, not an assertion that both arm durations are small.

## 2. The rare-arm expansion, including its degree bound

Write ell(v(B))=sum_(n=2)^m c_n log b_n(B), with c not zero and

    sum_n c_n binom(n,2)=0.                              (4)

There is a least k in {3,...,m} with

    M_k=sum_(n=2)^m c_n binom(n,k) != 0.                 (5)

Indeed the triangular matrix binom(n,j), 2<=j,n<=m, is invertible, and M_2=0 by (4).

Choose r in [0,1), z>0, and use the analytic parameterization

    x=r,  y=exp(-z epsilon),  g=epsilon.

The temporary value r=0 is used only to determine a coefficient sign. At the final witnesses r>0 and epsilon>0, so every physical parameter is strict. Factor (1) as

    b_n = exp(-z epsilon lambda_n) (1-epsilon)^n S_n,
    S_n = sum_(j=0)^n binom(n,j)
               (epsilon/(1-epsilon))^j r^binom(j,2)
               exp(z epsilon [jn-j(j+1)/2]).            (6)

All b_n equal one at epsilon=0, so their logarithms have real analytic extensions there. At any fixed expansion order h, the sum in (6) may be truncated to j<=h. Treating n as an indeterminate is legitimate: binom(n,j) is a polynomial, and for nonnegative integer n<j it vanishes.

The coefficient of epsilon^h in log S_n is a polynomial in n of degree at most h. To see this first for S_n, its j-th summand starts at order j with degree j from binom(n,j). Each further factor of epsilon from exp(z epsilon jn) adds at most one to the degree in n; the other factors add none. Products in the finite logarithm expansion preserve the same order/degree inequality.

For h>=2 the coefficient of epsilon^h in log b_n therefore has degree at most h. For h=1 it is -z lambda_n: the n epsilon term of log S_n cancels n log(1-epsilon)'s first term. Moreover b_0=b_1=1 identically. Thus each coefficient polynomial vanishes at n=0,1, and is a linear combination of binom(n,j), j>=2. All coefficients of orders h<k disappear after pairing with c.

To find the leading n^k coefficient at order epsilon^k, retain only the top n-degree contributions in (6). With a formal variable t=n epsilon these contributions are

    f_r(t exp(zt)),
    f_r(u)=sum_(j>=0) r^binom(j,2) u^j/j!.

The prefactors in (6) have n-degree at most two, so for k>=3 they do not contribute to n^k. Consequently, putting

    P_k(z,r)=[t^k] log f_r(t exp(zt)),

we obtain the exact asymptotic

    sum_n c_n log b_n(r,exp(-z epsilon),epsilon)
       = k! M_k P_k(z,r) epsilon^k + O(epsilon^(k+1)).   (7)

The coefficient P_k is a polynomial in z and r: only the first k terms of f_r and of the formal logarithm are required. Formula (7) concerns one shared source parameter triple throughout the whole diagonal profile.

## 3. A uniform coefficient sign change

At r=0, f_0(u)=1+u, so

    P_k(z,0)=sum_(l=1)^k (-1)^(l-1)
                l^(k-l-1) z^(k-l)/(k-l)!.              (8)

The leading coefficient is 1/(k-1)!, so P_k(z,0)>0 for sufficiently large positive z. In fact this leading coefficient is independent of r.

We prove a negative value for EVERY k>=3, rather than infer it from finitely many polynomials. Set

    z_k=(k-1) 2^(k-4)>0.

For k=3, P_3(1,0)=-1/6. For k=4, P_4(3,0)=-7/4.

Suppose k>=5. Divide (8) by its positive leading term z_k^(k-1)/(k-1)!. Its l=1 term is 1 and its l=2 term is -2. Discarding all the other negative terms only increases the sum. For an odd l>=3, the positive term ratio is at most

    R_l = l^(k-l-1) / 2^((k-4)(l-1)),                  (9)

because (k-1)!/(k-l)! <= (k-1)^(l-1). For l=3 this is (3/4)^(k-4)<=3/4. For l>=5, with l<=k,

    R_l = [l^(-1) 2^(-(l-4)(l-1))]
              [l/2^(l-1)]^(k-l)
         <= (1/5) 2^(-(l-1)).                          (10)

Here l/2^(l-1)<1 and (l-4)(l-1)>=l-1. Summing the latter bound over ALL integers l>=5, not just the odd ones that occur, gives 1/40. Therefore the normalized polynomial is at most

    1-2+3/4+1/40 = -9/40 < 0.                         (11)

This proves P_k(z_k,0)<0 uniformly in k.

By continuity in r, choose some strictly positive r<1 small enough that P_k(z_k,r)<0. For the SAME r, its positive leading z coefficient gives a positive z with P_k(z,r)>0. In (7), choose epsilon strictly positive and sufficiently small separately for those two z values. The leading nonzero coefficient fixes the desired signs (interchanging the witnesses if M_k<0). Equation (6) also gives b_2->1, so both witnesses can satisfy any prescribed pair-loss bound delta. Their x,y,g are all strictly between zero and one. This proves Theorem 1.

## 4. An exact finite-word consequence for the DIAGONAL projection

THEOREM 2. Fix m>=3 and delta>0. The additive semigroup of vectors (2) generated by strictly positive bigons with 1-b_2<delta is all of R^(m-2). In particular there is a nonempty finite strictly positive independent word with every bare bigon that weak, for which

    b_n = b_2^lambda_n,   2<=n<=m.                     (12)

The diagonal map has rank m-2 in defect coordinates at some such zero-defect word. Leading and inter-cell ordinary edges can be made strict; they leave every defect (2) unchanged. No bound on the sum of their pair hazards, or on the sum of the bigon pair hazards, follows.

Here is an elementary semigroup argument, included to expose the exact inference rather than import a generic controllability theorem. Let U_delta be the strict parameter domain with pair loss below delta. It is path connected: first raise both arm survivals toward one, then vary g, then reverse such an arm-raising path. More explicitly, two triples can be connected through a common arm pair sufficiently close to one, because increasing x,y decreases pair loss and sufficiently large common x,y work for all g in the connecting interval. This gives paths wholly inside U_delta. Also v tends to zero at its identity boundary.

The derivative vectors Dv(p)u, for p in U_delta and physical tangent vectors u, span R^(m-2). Otherwise a nonzero ell annihilates all of them, so ell(v) is constant on connected U_delta. Its identity-boundary limit makes that constant zero, contradicting Theorem 1. Choose finitely many such derivative vectors forming a basis. The sum of the corresponding bigon maps is a submersion. Its image contains a Euclidean ball B(a,rho), rho>0, contained in the additive semigroup S_delta, with a smooth local source section after selecting an invertible minor.

Theorem 1 and compactness of the unit sphere provide finitely many attainable vectors whose convex hull contains zero in its interior: for each unit functional select a vector where it is negative, then take a finite subcover. Hence their positive cone is the whole space. In particular write

    -a=sum_(j=1)^J alpha_j v_j,    alpha_j>=0.

For any large integer N, replace N alpha_j by its integer part n_j. The rounding error

    e_N=N a+sum_j n_j v_j

is bounded independently of N. The N-fold sum of B(a,rho), followed by these finitely many repeated v_j, contains B(e_N,N rho), and lies in S_delta. For sufficiently large N this ball contains a neighborhood of zero. An additive semigroup containing a neighborhood of zero is all of R^(m-2): for any target v, choose an integer M with v/M in that neighborhood and add M copies.

For the rank assertion, in the zero-centered construction choose the N ball terms to have the identical small displacement -e_N/N from a. This lies in the smooth submersion section for large N. The sum of their derivatives still spans the defect space. All the fixed rounding-correction cells remain untouched. Adding positive ordinary connectors realizes the same defect vector by an actual legal source chain.

This argument is closely related to the classical fact that an additive semigroup with interior and no containing halfspace is the whole vector group; compare Lawson, Maximal subsemigroups of Lie groups that are total (1987), Sections 3 and 5, DOI 10.1017/S0013091500026870. We use only the elementary argument above. No historical novelty is claimed.

## 5. Why this does not finish the graph target

1. Matching (12) does NOT imply matching complete labelled forests. The cap-four quotient already has the independent C,H coordinates in addition to its diagonal coordinates.
2. The number of cells and total pair hazard in Theorem 2 can depend on m and delta. Small loss of each factor does not bound their sum. In particular this does not construct rivals to one FIXED E(1/32) at every cap.
3. These are private unmarked natural independent kernels. Internal forcing IDs, paired mechanisms, tied fresh positions or new observation channels have not been added.
4. Arbitrary log-defect vectors are attained with SOME source survival scale; the theorem does not prescribe all b_n independently at a fixed b_2.
5. No full-source witness budget, total G3 recognizer, critical-fibre classification, or G4 fixed-target conclusion follows. The point is to remove a diagonal-character obstruction from the actual all-cap construction, so the remaining work has to use full-forest directions and the required time budget.
