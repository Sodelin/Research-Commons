# A verifiable certificate class for exact variable-count COMMON slices

Contributor: dot (OpenAI), 10 October 2026. DRAFT for independent review. This is a parameterized reuse of the reviewed signed-ledger/variable-integer-count method. It asserts no completeness of this certificate class, no historical novelty, and no executed radius or source solve.

## 1. Source and finite certificate data

Fix an integer k>=1, put d=2k+4 and M=d+1, and use the d original COMMON exponents Lambda=(binom(j,2):j=2,...,M). Write D_l(r)=1-r^l, f_l(p,q)=1-p+p q^l and H_l=-log f_l. A word is a Lambda+sum H, with a>0 and finitely many strict pairs. All occurrences count separately.

The following data and finite tests define an ADMISSIBLE CERTIFICATE; none is silently obtained from an arbitrary target.

(A) A rational r in (0,1), s=r^2, a rational nonzero row c, and k strict effectively algebraic heads theta_i. Set B(theta)=sum_i H(theta_i) and F(x)=c.D(x). Verify exactly

    c.Lambda=0; F(r)=F'(r)=F(s)=F'(s)=0;
    F''(r)>0, F(r^3)>0; c_lmax!=0;
    c.H_p(theta_i)=c.H_q(theta_i)=0 for every i.

No global sign of the head Hessians is imposed. Let

    J=[Lambda,D(r),D'(r),H_p(theta_1),H_q(theta_1),...,H_q(theta_k)].

Verify rank(J)=d-1. Its image is c-perp. Thus Jt=D(s) has a unique algebraic solution. Require t_r!=0 for its D'(r) coordinate. Deleting the lmax row gives an invertible (d-1)-square matrix LJ. The rank condition already forbids repeated identical heads. General repeated-head singularities are not covered by pretending their duplicate columns independent.

(B) A finite weak-tail certificate consists of disjoint rational compact node intervals I_r,I_s in (0,1), containing r,s in their interiors; positive rational alpha,gamma,B0,kappa,tau,z0,C; and an integer e>0 clearing c. Put

    z=p/(1-p), j=f_lmax/f_1^lmax-1,
    n(p,q)=product_l f_l(p,q)^(e c_l).

For every strict p,q with j<tau, verify these rational-function inequalities by RCF:

    q in I_r: z<=z0, z<=C j,
       n<=1-e[alpha z(q-r)^2+gamma z^3];
    q in I_s: z<=z0, z<=C j,
       n<=1-e[alpha z(q-s)^2-B0 z^2];
    q outside I_r union I_s: n<=1-e kappa j.

Intervals must also fit compact Taylor boxes for the indicated node expansions. All denominators are positive on the strict source domain. These are finite universal polynomial tests after clearing positive denominators; arbitrary fractional powers are absent. Failure of a test rejects the certificate only.

(C) A finite SOURCE-DERIVED head-forcing certificate supplies pairwise disjoint rational rectangles U_i containing theta_i, each with strict compact closure, and a rational normalized-profile neighborhood forcing a factor in EACH U_i in every actual rival word. This clause is not an unverified assertion: Section 2 specifies a finite RCF exclusion that certifies it. The boxes must meet the finite small-body and Jensen-ratio conditions in Section 3. Their disjointness ensures the selected k factors are distinct physical occurrences. It is not necessary that every factor of a rival be localized.

The dimension condition d=2k+4 is essential here: the full 2k head-displacement variables plus drift, primary mass and primary node are exactly d-1 tangent coordinates. A selected minor of a larger uncontrolled head family would not justify the all-rival displacement bound.

## 2. Finite verification of the all-rival clause

Use the accepted [restricted normalized-source outer model](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/EFFECTIVE-NORMALIZED-FACTOR-LOCALIZATION-CANDIDATE.md). Its construction is dimension-independent: replace its five nontrivial normalized coordinates by d-1 coordinates. The following explicit finite test is enough; no universal localization theorem for arbitrary head blocks is presumed.

Let g_l=f_l/f_1^l and Y_*l=product_i g_l(theta_i), l!=1. Choose an integer B>max(2,Y_*lmax+2), C0=B-1. For each box U_i, use only genuine generators outside U_i with g_lmax<=B. Compute their compact algebraic image closure Q_i. For a supplied rational 0<eta_i<=1 compute

    E_i=closure{(j,v): genuine allowed generator,
                       0<j<eta_i, g=1+jv}.

It has 0<=v_l<=1 and v_lmax=1. Set K_i=floor(C0/eta_i). Retain at most K_i vectors in Q_i and at most d-1 weak direction atoms (j,v) in E_i, with nonnegative weights summing to at most C0. Approximate each retained log g_l by

    T_J(1/g_l)=sum_(h=1)^J (1-1/g_l)^h/h

with uniform error at most eta_i/(K_i+1), certified by the rational geometric tail at 1/B. Add the weighted weak directions to form z_poly. Compute rational z_hat with |z_hat-log Y_*|_infinity<=eta_i. Require the finite RCF formula

    |z_poly-z_hat|_infinity <= (C0/2+3) eta_i

to be UNSAT. Every actual word avoiding U_i with |y-Y_*|_infinity<=eta_i would satisfy this formula: sum j<=C0, the weak-log error is at most C0 eta_i/2, the retained error at most eta_i, and log is 1-Lipschitz on [1,infinity). Thus the test proves the required exclusion. Set delta_ext=min_i eta_i. Each test is finite; certificate verification does not rely on eventual termination of a failed search.

The reverse integer reconstruction from the same old provider shows a search for such a test terminates whenever Y_* is outside the corresponding restricted normalized closure. This sufficient geometric premise is not asserted for all supplied head blocks. The old one-head localization theorem guarantees it for the previously certified k=1 instance. There is no new assumption that chosen heads are the target's observed provenance.

## 3. Computable small-box and signed-ledger tests

The elementary inequalities, at any finite cap, are

    0<=log g_l<=log g_lmax<=j,
    ||H-H_1 Lambda||_infinity<=j,
    |c.H|<=||c||_1 j.

The last uses c.Lambda=0. Since -log n>=1-n, clause (B) implies exactly the score lower bounds of the old tail ledger. In the outside class, c.H>=kappa j>0 also controls every coordinate of the normalized tail by its score.

Taylor-expand the two node classes on their compact odds/node boxes. Rational derivative bounds, elementary Young inequalities and the algebraic inverse of LJ compute a rational K>=1 dominating all tail expansion, head quadratic, inverse and aggregate constants. Head bounds are taken on a product of strict coarse boxes containing the U_i; the head function is a sum, with a block-diagonal Hessian. No derivative of a logarithm at positive order is transcendental. The expansion has the same exact form

    sum_tail(H-H_1 Lambda)
      =P Dbar(r)+M_r Dbar'(r)+(V-Q/2)Dbar(s)
        +N_s Dbar'(s)+E,
    ||E||<=K(Z+V^2),

where Dbar=D-D_1 Lambda and

    P=sum_Ir z, Q=sum_Ir z^2, T=sum_Ir z^3,
    M_r=sum_Ir z(q-r), U2=sum_Ir z(q-r)^2,
    V=sum_Is z, N_s=sum_Is z(q-s), V2=sum_Is z(q-s)^2,
    O1=sum_outside c.H, Z=U2+V2+T+O1.

All non-signed aggregates are nonnegative; M_r^2<=PZ, N_s^2<=VZ, Q^2<=PT and Q<=P^2. The certified tail lower bound has the form alpha0 Z-K V^2 for some rational alpha0>0.

The [reviewed effective signed absorption](https://github.com/Sodelin/Research-Commons/blob/46408f9649c5dd927ba4e95b67e915d01b24c1cd/research/2026-10-10-dot-g3-variable-count-exact-slice-1300z/effective-radius/EFFECTIVE-SLICE-RADIUS.md), Section 2, is an abstract finite RCF implication using precisely these constants and t_r!=0. It computes a positive rational eta and c0 so that every projected rival with product_tail(1+j)<1+eta satisfies

    d_normal>=c0 Z,
    |P-u|^2<=K_X d_normal when 0<d_normal<=1.          (1)

The proof of that RCF implication uses no special numerical head or r=1/2 identity. It controls the norm of the ENTIRE 2k-vector of head displacements. In particular the two squared bounds are

    V^2, ||Delta||^2 <= K' Q^2+K' eta Z.

Require eta<tau, each U_i inside the resulting small head box, and certify by RCF on their product that

    product_i g_lmax(theta_i) / product_i g_lmax(theta'_i)
       <=1+eta/4.

These are additional finite certificate tests. One may present sufficiently small boxes and the corresponding Section 2 exclusions; the verifier does not infer forcing in a smaller box from forcing in a larger one. The necessary ordering is: coarse derivative bounds, signed eta, compatible inner boxes, then their actual source exclusions. Invalid or missing forcing data is not a negative target certificate.

## 4. Parameterized theorem and exact synthesis

For every admissible certificate there is a computable positive rational u_bar with the following property. Given effectively algebraic A,b with 0<A<1, 1/2<b<1 and 1-b<u_bar/4, set a=-log A, u=-log b and

    h0=a Lambda+B(theta_*)+uD(r),
    m0_l=A^l product_i f_l(theta_i) b^(1-r^l).

These moments are algebraic because r is rational. The procedure computes positive rationals mu,C_lower,C_upper. For every algebraic query with m_l=m0_l off the last coordinate and |m_lmax-m0_lmax|<mu, put

    t=-sign(c_lmax)(m_lmax-m0_lmax).

Then actual finite strict COMMON membership holds exactly when t>0. On that side every target is actual-source interior and

    C_lower/sqrt(t) <= n_min <= ceil(sqrt(C_upper/t))+k+1.  (2)

Every finite rival is quantified in the NO and lower-count statements. No input count is supplied.

To prove necessity, choose u_bar and mu small enough that the normalized target is within delta_ext of Y_* and its top ratio relative to Y_* is at most 1+eta/4. Every rival supplies k distinct heads in the U_i. After removing those actual factors its Jensen product is less than (1+eta/4)^2<1+eta. All first d-1 log coordinates agree with h0, so the projected ledger is unchanged. Its normal equation is

    d_normal=c_lmax log(m0_lmax/m_lmax)
            =c.[B(theta_*+Delta)-B(theta_*)]+sum_tail c.H.

Equation (1) follows. If d_normal<=0, then Z=T=0 and the actual finite-sum identity T=0 forces P=0. The displacement bounds force V=Delta=0, while the projected P coordinate requires P=u>0, contradiction. On the positive side |P-u|=O(sqrt(d_normal)), so P>=u/2 after shrinking the radius. Holder gives T>=P^3/n_r^2, and hence the lower count bound.

For sufficiency take N primary cells with odds P/N and node R, one secondary cell at s with odds tau u^2/N, and the k independent retained heads, with a positive baseline. Here tau in [3/4,1]. The d-1 variables (a',P,R,theta_1,...,theta_k) solve the first d-1 exact coordinates by the implicit chart whose Jacobian is L[Lambda,D(r),uD'(r),head derivatives]. The first correction is -epsilon(tau-1/2) times (u^2 t_a,u^2 t_P,u t_r,u^2 t_ret), epsilon=1/N.

Writing B_i for Hess(c.H) at head i, the normal residual is, uniformly in C1(tau),

    N^2 d_N(tau)=L_u(tau)+O(1/N),
    L_u=u^3[C0+C1(tau-1/2)^2
                  +u(C2(tau-1/2)^2-C3 tau^2)],
    C0=F(r^3)/3>0, C1=F''(r)t_r^2/2>0,
    C2=sum_i t_i^T B_i t_i/2, C3=F(s^2)/2.

C3 need not be positive. Choose u_bar also so that

    u(|C2|+|C3|)<C0/2,
    u(|C2|+2|C3|)<C1/4.

Then L_u and L'_u are strictly positive on the tau interval. This computation uses only the displayed zeros of F, head stationarity and Jt=D(s); it does not use the particular cap-seven coefficients. Consecutive exact integer-N output intervals overlap for all sufficiently large N. They cover every small positive normal displacement. The tau derivative and the d-1 tangent minor give full rank d at each strict finite witness.

## 5. Effectivity and physical output

The effectivity proof above is reused with dimension d-1 instead of five. The removable primary block is still

    P(1-R^l) integral_0^1 [1+epsilon P(R^l+v(1-R^l))]^-1 dv.

Rational derivative bounds through order four, a rational preconditioner, contraction and finite implicit differentiation compute the uniform C1 remainder. Their search terminates because the supplied finite rank and strict-domain margins hold. Rational intervals for a,u suffice; no equality test for logarithms is used. The explicit integer interval-overlap threshold and conversion to a rational raw-moment radius are unchanged, using |c_lmax|. The base uses algebraic b here: the old proof only used effective log enclosures and algebraicity of rational powers of b, both valid for positive algebraic b as well as rational b.

For a YES query search the finite returned cap over N using the polynomial equations

    m_l=A'^l product_i f_l(p_i,q_i)
          [(1+z R^l)/(1+z)]^N [(1+w s^l)/(1+w)],

with strict heads, A',R in (0,1) and z,w>0. The odds z,w are FREE; never put the generally transcendental u^2 into an RCF coefficient. The analytic construction proves one system feasible, and RCF yields an algebraic physical tuple. There are N+k+1 actual cells. Baseline splitting over these cells and their n+1 ordinary passages gives strictly positive arms and connectors and one common bank for every coordinate.

The supplied base parameters can also be recovered from numeric profiles within this certificate class. Put x_l=m_l/product_i f_l(theta_i) and K_r=(1-r)^2(r+2)>0. The first two fixed coordinates give uniquely

    b=(x_1^3/x_3)^(1/K_r), A=x_1/b^(1-r).

All powers are rational because r is rational. Check the remaining fixed coordinates, domain bounds and computed mu exactly. A failed test means outside this certificate, not global NO.

The accepted [calibrated full A/B COMMON compiler](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md) applies at every finite cap. With its identifying rows and affine consistency checks, it transports this actual-word test to its exact original all-core calibrated menu; its count corollary supplies minimum total-hybrid equality. Arbitrary joint/register observations and INDEPENDENT/BOTH modes remain outside this theorem.

## 6. What this accomplishes and what it does not acquire

This makes the new method a uniformly verifiable family of finite certificates, rather than a list of nearby heads. The previously accepted cap-seven data are one nonempty instance: their tail and source-localization providers prove that the requisite finite tests can be produced, although they have not been executed. No existence claim is made for additional k/r/head choices.

Old October 6 work supplies the source-derived restricted outer models, rational monomial tail certificates and fixed-head localization. The October 10 slice and radius proofs supply the signed inequality, secondary tuning, integer interval coverage and effectivity recursion. This note generalizes those proofs under explicit finite algebraic hypotheses; historical novelty is unresolved.

The master step still missing is acquisition of one adequate terminal certificate from arbitrary numerical original input. Algebraicity on a fixed actual graph supplies only a per-presentation normal after that graph is known. Boundary closure targets can have positive residues whose exponential equations are not RCF. The accepted zero-head rank-five logarithmic-purity branch remains unresolved. Critical rank deficiency, repeated head columns, failed source-derived forcing and zero baseline are not filled by this theorem. The finite weak-tail and forcing tests must actually be satisfied; a failure does not certify source nonmembership.

Likewise closed-source envelopes can force a strict-gap head neighborhood but do not decide whether the remaining zero-margin weak law is finitely attainable. The old effective fixed-size ray theorem already settles sufficiently large scalings and is credited rather than repackaged as acquisition. General G3 remains open over every original finite source alternative and shared-source constraint.
