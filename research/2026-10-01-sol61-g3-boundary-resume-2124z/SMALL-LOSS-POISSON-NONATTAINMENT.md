# A global paired-normal small-loss obstruction at cap seven

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 23:55 UTC.
Status: hand argument and executed exact rational/polynomial constant certificate independently accepted locally by the current head; immutable public review receipt pending. Explicit example b=1-2^(-175). Public research publication authorized again on2026-10-02. Arbitrary-cap finite-input recognition remains open.

## 1. Precise proposed theorem

Fix r=1/2, s=r^2=1/4 and lambda=(1,3,6,10,15,21), cap M=7. There is a constant C_*>0 such that for EVERY a,w>0 with a+w<C_*,

    h=a lambda+w R(r)

belongs to the ACTUAL common-chain closure and the ordinary moment interior, but is NOT the log signature of any finite strict positive common Bernoulli-chain source, regardless of factor count. Its consistent extension gives the same rejection at every cap M>=7.

This is a SMALL-LOSS paired-normal theorem, not a global linear separator. Each individual normal can change sign on genuine Bernoulli factors. Their simultaneous zero equations, the total loss budget and Cauchy make the combined obstruction global.

## 2. Exact sparse polynomials and factor projections

Let F0(q)=sum c0_j(1-q^lambda_j), with c0 supported on1,3,6,10, and F1(q)=sum c1_j(1-q^lambda_j), supported on all six exponents. Normalize both constants Fk(0)=sum c_k,j=1. Require both to have double roots at1,r, and F1 also a double root at s. The exact rational coefficients are preserved in paired-normal-algebra.json. Their factorizations are

    F0=(q-1)^2(2q-1)^2 Q0(q)/4724,
    Q0=1848q^6+5544q^5+10626q^4+16632q^3
        +17554q^2+13161q+4724,

    F1=(q-1)^2(2q-1)^2(4q-1)^2 Q1(q)/1016736430620,

where every coefficient of the degree15 Q1 is strictly positive (full coefficients in the JSON). Thus F0>0 on[0,1) except r, and F1>0 on[0,1) except r,s. Both are nonnegative on[0,1] and have exactly the stated double roots. In particular F0''(1),F1''(1)>0, c0.lambda=c1.lambda=0, and c0.R(r)=c1.R(r)=0.

For a strict factor define a_j(q)=1-q^lambda_j and

    Lk(p,q)=c_k.H(p,q)=sum_j c_k,j[-log(1-p a_j(q))].

Write Bk=sum_j|c_k,j|, and T_k,n(q)=sum_j c_k,j a_j(q)^n. For0<=p<=1/2 the log expansion is uniform on0<=q<=1:

    Lk=p Fk(q)+p^2 T_k,2(q)/2+p^3 T_k,3(q)/3+O(p^4),
    |sum_(n>=2) p^n T_k,n/n|<=Bk p^2,
    |sum_(n>=4) p^n T_k,n/n|<=Bk p^4/2.

The bounds use|T_k,n|<=Bk and the elementary geometric-series majorants. Exact polynomial identities give

    T_k,2(q)=2Fk(q)-Fk(q^2),
    T_k,3(q)=3Fk(q)-3Fk(q^2)+Fk(q^3).

## 3. Uniform positivity near q=1, including p near one

The small-p series alone is inadequate for q near one. There the strict loss p(1-q) can be small even when p is near one. Handle this region separately.

For each k, Lk is analytic on a neighborhood of the compact rectangle p in[0,1], q sufficiently near1: the finitely many f_j=1-p+p q^lambda_j stay uniformly nonzero. Lk vanishes at p=0; at p=1 it is(-log q)c_k.lambda=0; it vanishes at q=1 with its first q derivative because c_k.lambda=0. Analytic division therefore yields

    Lk(p,q)=p(1-p)(1-q)^2 Ak(p,q),

with Ak analytic on a uniform compact neighborhood. At q=1,

    Ak(p,1)=-sum_j c_k,j lambda_j^2/2=Fk''(1)/2>0,

independent of p. By compactness there is Q<1 such that BOTH Ak are positive for p in[0,1], q in[Q,1]. Consequently both Lk are STRICTLY positive for every0<p<1 and Q<q<1. Choose Q>r and large enough to contain disjoint neighborhoods below it in the next section.

This positivity was certified without differentiating a logarithmic quotient: partial_q^2 Lk divided by p(1-p) is a rational function with a continuous extension at p=0,1, and its normalized polynomial numerator equals Fk''(1)>0 at q=1. The executed coefficient-Lipschitz bounds give a common rational Q (recorded in paired-normal-certificate.json) with uniform positivity. Together with Lk=Lk,q=0 at q=1, twice integration gives the stated strict sign. The exact rational-Q extraction is EXECUTED; the all-parameter integration argument remains hand mathematics.

## 4. Two disjoint root neighborhoods and fixed positive constants

Choose small closed disjoint intervals U about r and V about s, both contained in(0,Q). Shrink U until the following polynomial bounds hold, for some A,D,K>0:

    F1(q)>=(A)(q-r)^2 on U,
    |T_1,2(q)|<=D(q-r)^2 on U,
    T_1,3(q)>=K on U.

These constants exist: F1/(q-r)^2 is positive at r; T_1,2 is divisible by(q-r)^2 because both F1(q) and F1(q^2) vanish doubly there; and T_1,3(r)=F1(r^3)>0 since r^3 differs from1,r,s.

Use the uniform Taylor bounds to choose p0>0, at most1/2, small enough that on U,

    L1(p,q)>=(A/2)p(q-r)^2+(K/6)p^3>=gamma p^3,
    gamma=K/6>0,
    L0(p,q)>=-B0 p^2.

For example it suffices for the first line that p0<=A/D when D>0 and p0<=K/(3B1). The L0 bound follows directly from F0>=0 and the second-order majorant.

On V, F0 has a strictly positive minimum; by making p0 smaller,

    L0(p,q)>=delta p, delta>0,
    L1(p,q)>=-B1 p^2.

On the compact set[0,Q] outside the INTERIOR of U, F0 has a strictly positive minimum. On[0,Q] outside the union of the INTERIORS of U and V, F1 has a strictly positive minimum. Make p0 smaller once more to ensure L0>0 outside U and L1>=0 outside U union V for all0<p<=p0 there. Section3 handles q>Q for every strict p. The closed complements also cover root-interval boundary points, so the partition in the sum is unambiguous. All constants/intervals are chosen once, independently of chain size and target a,w.

## 5. The budget converts these factorwise estimates into an all-N rejection

Assume for contradiction a strict finite chain realizes h. Its own baseline need not equal a. Write its log signature

    h=a'lambda+sum_i H(p_i,q_i), a'>0.

Its first coordinate gives a'+sum_i H2=a+w=C. Therefore

    sum_i p_i(1-q_i)<=C,
    p_i<=C/(1-Q) whenever q_i<=Q.

Require C<=p0(1-Q). Then every factor below Q satisfies all estimates of Section4. Factors above Q satisfy Section3, regardless of p.

Both normals annihilate the TARGET h and ANY baseline a'lambda, so

    sum_i L0(p_i,q_i)=sum_i L1(p_i,q_i)=0.

Let

    P_U=sum_(q_i in U) p_i,
    Q_U=sum_(q_i in U) p_i^2,
    T_U=sum_(q_i in U) p_i^3,
    P_V=sum_(q_i in V) p_i.

The first normal's lower bounds give delta P_V<=B0 Q_U. The second gives

    0=sum_i L1 >= gamma T_U-B1 sum_(q_i in V) p_i^2
               >= gamma T_U-B1 P_V^2
               >= gamma T_U-B1(B0/delta)^2 Q_U^2.

Cauchy-Schwarz gives Q_U^2<=P_U T_U. If q_U=max U<1, the loss budget gives P_U<=C/(1-q_U). Consequently

    0 >= [gamma-B1(B0/delta)^2 C/(1-q_U)] T_U.

Choose, for example,

    C_* = min(p0(1-Q), gamma(1-q_U)/[2B1(B0/delta)^2])>0.

For0<C<C_*, the bracket is positive, so T_U=0 and there are no factors in U. The first normal is then STRICTLY positive on EVERY remaining strict factor, so its zero equation forces there to be no factors at all. Only the chain baseline remains. That is impossible: the target has h3=3a+w(1+r+r^2)<3(a+w)=3h2, while every pure baseline has h3=3h2. Contradiction. QED conditional only on the already proved factorwise compact/Taylor premises.

No ordinary-law support is used as an actual source factorization, no negative probabilities or fractional counts occur, and no restriction is placed on finite factor count. The total positive baseline merely consumes part of the budget; its normal projections vanish.

## 6. Actual closure, ordinary interior, and exact algebraic target family

Closure: keep A=exp(-a) strictly positive and less than one, set p_N=w/[N(1-r)], q=r, and use N strict factors for sufficiently large N. Their log signatures converge to a lambda+w R(r), by the established strict Poisson approximation. This asserts actual closure, not actual attainment.

Ordinary interior: the signature is the moment vector of X=A r^K for K Poisson with positive parameter w/(1-r). Its support has infinitely many distinct points in(0,A], each with positive probability. A nonzero finite polynomial in span(1,x^lambda_j) cannot vanish on that infinite support (ordinary polynomial root finiteness suffices). A supporting nonnegative ordinary-moment functional with zero expectation would have to vanish there. Thus no proper supporting functional exists, and the finite moment vector is ordinary-moment interior. This is an ordinary probability-law argument, not a claim that this law is an actual finite source.

To obtain exact ALGEBRAIC input signatures, choose a rational b in(0,1) sufficiently close to one, put a=w=-log b, and set

    m_j=b^(lambda_j+R_j(1/2)).

Every exponent is rational, so every m_j is a positive algebraic number in(0,1). The exact certificate NOW extracts b=1-2^(-175) and verifies4*2^(-175)<C_*. Since -log(1-x)<=x/(1-x)<=2x for0<x<=1/2, the example has2(-log b)<=4*2^(-175)<C_*. It is therefore a CONCRETE algebraic NO instance, conditional on the hand proof. A compact exact real-algebraic encoding is z0=b, z_(k+1)>0 with z_(k+1)^2=z_k, then m_lambda=b^(lambda+2)/z_(lambda-1). No enormous expanded minimal polynomial was generated.

Restriction to the cap-seven coordinates excludes any finite actual factorization at every larger supplied cap, while the same infinite ordinary support keeps ordinary-moment interior at every finite cap.

## 7. Verification and unresolved master scope

Executed exact algebra: two rational normals at r=1/2, their sparse annihilation equations and positive-coefficient polynomial factorizations, under paired-normal-algebra.json; then the exact rational constants and normalized Lqq polynomial numerators in paired-normal-certificate.json. The latter standalone checker passed in0.58seconds, Python3.12.14/SymPy1.14.0, with no floating fit or factor-size census. It derives rational Q by coefficient Lipschitz bounds, root neighborhoods/Taylor constants and C_*; it extracts b=1-2^(-175). Finite polynomial/rational premises are tested exactly. The summation/Cauchy/nonattainment, actual closure and ordinary interior arguments remain hand proofs; no formal Lean proof claimed. The current head independently accepted the explicit certificate SHA2562a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118 and the complete scoped NO argument, and reported an independent verifier SHA256330caa40b9eb9362525f43ca585163b2f5b9fb5992b18acdc7ee758374bf7b86. The public receipt is coordinated separately; preservation itself does not establish truth.

This does not decide all finite algebraic common-source inputs or the separate cap-eight/nine killing candidate. It would refute the conjecture that every ordinary-moment-interior point of the actual closure is attained, while yielding one global source-faithful boundary NO family. No historical novelty claim or finite-input undecidability reduction is made.

## 8. A finite algebraic-input NO predicate

The paired-normal proof actually rejects any positive signature satisfying its two normal equations and small-loss bound, unless it is a pure baseline. It does not need the Poisson formula for this rejection.

Require0<m_j<1 for every supplied coordinate. Clear denominators of c0,c1 to get integer rows e0,e1. The equalities c_k.h=0 are precisely

    product_(e_k,j>0) m_j^(e_k,j)
      =product_(e_k,j<0) m_j^(-e_k,j).

These are exact finite algebraic equalities on supplied positive algebraic inputs, rather than undecided log evaluations. For the rational C_* from the checker, require m2>1-C_*/2 (C_*<1); then m2>1/2 and -log m2<=2(1-m2)<C_*. Require also that at least one m_j differs from m2^lambda_j. All three conditions give a FINITE exact actual-source NO certificate at cap seven, or by restriction at a higher cap.

For the concrete Poisson example m2=b^2. Its rational comparison with1-C_*/2 is checked in the supplementary instance record. The two signed-monomial equalities follow from the exact rational exponent identities e_k.(lambda+R(r))=0; nonbaseline follows already at lambda=3 because its exponent19/4 differs from6. This predicate does not decide inputs outside the certified band/variety intersection.
