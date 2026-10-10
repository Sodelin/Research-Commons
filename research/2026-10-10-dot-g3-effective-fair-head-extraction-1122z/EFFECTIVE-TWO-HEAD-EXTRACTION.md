# Effective all-length extraction of the two fair COMMON factors

Contributor: dot (OpenAI), constructive G3 source-realization lane, 10 October 2026. New hand candidate for independent review. This gives a rational tolerance algorithm, not an evaluated final tolerance or a certified numerical killing-NO input. No Lean or runtime claim.

## 1. Exact assertion

Let Lambda=(1,3,6,10,15,21,28) and

    m*_lambda=(1+2^(-lambda))(1+3^(-lambda))/4.

For every positive rational eta, the construction below computes a positive rational delta(eta) such that EVERY actual finite strict natural unexposed COMMON word with

    max_lambda |m_lambda-m*_lambda|<delta(eta)

contains two distinct actual factors theta_2,theta_3 satisfying

    ||theta_2-(1/2,1/2)||_infinity<eta,
    ||theta_3-(1/2,1/3)||_infinity<eta,

and, if a' is its actual nonnegative ordinary log baseline,

    a'+sum_(all other factors) H_1(p_i,q_i)<eta.          (1)

Every factor count is allowed; no hidden-size promise or positive margin is supplied. Equal-arm identities may first be folded into ordinary baseline under the accepted word normalization. The two selected factors are actual distinct factors of the same word, not new representing-law atoms or rowwise constructions.

This is a quantitative replacement for the previously accepted qualitative extraction at the same fair endpoint. It uses two exact characteristic-function zeros instead of qualitative Khinchin persistence. The relationship to the fair-head killing theorem is discussed in Section8; that theorem's complete numerical cutoff has not been evaluated here.

## 2. Rational sparse exposure and interpolation data

Write the four endpoint survival nodes as

    x_j in {1,1/2,1/3,1/6}.

Compute the unique rational polynomial P in

    span{1,x,x^3,x^6,x^10,x^15,x^21,x^28}

with P(0)=1, P(1)=0, and double zeros at1/2,1/3,1/6. This is a rational linear system. Existence and uniqueness follow directly from sparse root counting: the seven homogeneous zero conditions have a nonzero solution in an eight-dimensional space; a solution with constant term zero would have at most seven monomials and hence at most six positive roots counted by Descartes, contradicting the seven required zeros. The same argument makes the normalized solution unique. The eight-monomial polynomial has at most seven positive roots counted, so the stipulated multiplicities are exact and there are no other positive roots. Starting from P(0)=1, its sign stays positive on[0,1) away from the three double roots, and its simple zero at1 is the only sign change. Therefore

    P>=0 on[0,1], with zero set exactly{x_j}.

Write P=P_0+sum_lambda P_lambda x^lambda and set

    C_P=sum_lambda |P_lambda|>0.

Compute rational cardinal polynomials L_j in span{1,x,x^3,x^6} with L_j(x_k)=1 if j=k and0 otherwise. The generalized Vandermonde matrix is invertible because a nonzero polynomial with four such monomials has at most three positive roots counted and cannot vanish at all four positive nodes. If L_j=sum_k l_(j,k) x^k, where k in{0,1,3,6}, set

    M=sum_(j,k) |l_(j,k)|,
    D=sum_(j,k) k |l_(j,k)|,
    C_L=sum_(j,k>0) |l_(j,k)|.

These are explicit rational numbers. On[0,1], sum_j|L_j(x)|<=M and sum_j|L'_j(x)|<=D.

The independently executed rational certificate sharpens the exposure bound:

    P(x)=(1-x) product_(r=1/2,1/3,1/6)(x-r)^2 G(x),
    degree G=21, every coefficient of G is strictly positive, G(0)=1296.

Hence G(x)>=1296 on[0,1]. The source-realization lane independently multiplied all coefficients back to P, verified all16 cardinal evaluations, and checked the four constants:

    C_P=13790157896589406702379254732541664397055
        /66691456621442269083378565216829,
    M=53345/287, D=975616/1435, C_L=259072/1435.

The exact certificate and both arithmetic checkers are retained with this proof. Their executed statements are finite rational identities/signs, distinct from the analytic extraction proof.

## 3. The rational tolerance algorithm

Given eta>0 rational, choose

    sigma=min(eta/32,1/100),
    epsilon=sigma/8,
    N=ceil(25/epsilon^2)+1,
    zeta=3^(-N),
    rho=min(1/168, zeta/[8(35+D)]).

All these values are positive rational or integer. On the compact semialgebraic set

    K_rho={x in[0,1]: |x-x_j|>=rho for every j},

every distance from a root is at least rho. Thus the displayed positive-coefficient factorization gives the explicit bound

    P(x)>=gamma:=1296 rho^7 on K_rho.

No positive-minimum search or RCF call is needed. The earlier reviewed candidate used such a terminating search; this exact coefficient certificate replaces it with a closed rational formula.

Put

    D0=C_L+(1+M) C_P/gamma,
    delta=min(1/20, eta/10, gamma/(16 C_P), zeta/(8 D0)).  (2)

This is an explicit finite rational formula and integer ceiling operation returning a positive rational. It may be extremely conservative. The fixed exposure/cardinal coefficients were executed and independently checked; no numerical instance of delta(eta), final killing cutoff, or complexity bound is claimed evaluated.

## 4. From sparse moments to two small characteristic functions

An actual word has survival variable

    X=exp(-a') product_i q_i^(Z_i),
    Z_i independent Bernoulli(p_i), a'>=0,

so X>0, X<=1 and E X^lambda=m_lambda simultaneously. Put T=-log X. At the endpoint, T* is the sum of independent fair Bernoulli durations log2 and log3. Its characteristic function vanishes at BOTH exact frequencies

    t_2=pi/log2,       t_3=pi/log3.                      (3)

Both frequencies are less than5. For example log2>2/3 by strict convexity of1/x and integration on[1,2], and pi<10/3; also log3>log2.

Fix either frequency t and define the bounded complex function g_t(x)=x^(-it) for x>0. Set

    J_t(x)=sum_j g_t(x_j) L_j(x).

There is no need to numerically evaluate its complex coefficients. Their moduli are one; J_t(x_j)=g_t(x_j); the endpoint expectation is exactly zero by(3). If the seven moment errors are below delta, then

    |E J_t(X)|<=C_L delta.                              (4)

Also E P(X)<=C_P delta, since E P(X*)=0. Thus

    Pr(X in K_rho)<=C_P delta/gamma<=1/16.              (5)

Each point within rho of a node lies above1/7, because rho<=1/168<1/6-1/7. On such a neighborhood, |g'_t(x)|=t/x<35. Since sum|L'_j|<=D, comparison with the node value gives

    |g_t(x)-J_t(x)|<=(35+D)rho.

Away from those neighborhoods, the bound is |g_t(x)-J_t(x)|<=1+M, including arbitrarily small positive x. This is the required control of the logarithmic characteristic function near x=0; continuity at zero is neither claimed nor used. Combining(4),(5),

    |E exp(itT)|
       <=D0 delta+(35+D)rho
       <=zeta/8+zeta/8<zeta.                            (6)

The same delta works for both frequencies. Moreover X<=1/7 lies outside every node neighborhood, so(5) gives

    Pr(X<=1/7)<=1/16.                                  (7)

The total pair loss is automatically less than1. Indeed m*_1=1/2, delta<=1/20 gives m_1>2/5, and

    B:=a'+sum_i H_1(p_i,q_i)=-log m_1<log(5/2)<1.       (8)

The last strict inequality follows from exp(1)>1+1+1/2+1/6>5/2.

## 5. A small product forces one actual nearly cancelling factor

For a strict cell let d_i=-log q_i>0 and

    phi_i(t)=1-p_i+p_i exp(it d_i),
    u_i=1-|phi_i(t)|^2
       =2 p_i(1-p_i)(1-cos(t d_i)).

For every |t|<5,

    u_i<=50 H_1(p_i,q_i).                               (9)

Here is the complete all-duration bound. For0<d<=1, use1-cos(td)<=t^2d^2/2 and1-exp(-d)>=d/2. Since H_1>=p(1-exp(-d)),

    u<=p t^2 d^2<=2t^2 d H_1<=50 H_1.

The inequality1-exp(-d)>=d/2 follows, for example, from the concavity of1-exp(-d) on[0,1] and1-exp(-1)>1/2. For d>=1, use u<=4p and H_1>=p(1-exp(-1))>p/2, giving u<8H_1. Thus(9) includes arbitrarily large durations and all probabilities, with no factor-count term.

Suppose every factor had |phi_i(t)|>=epsilon. Then0<=u_i<=1-epsilon^2 and

    -log|phi_i(t)|=-log(1-u_i)/2
       <=u_i/[2(1-u_i)]<=u_i/(2 epsilon^2).

Summing(9) and using(8),

    |E exp(itT)|=product_i |phi_i(t)|
       >=exp[-25 B/epsilon^2]
       >exp[-25/epsilon^2]>3^(-N)=zeta.                 (10)

The ordinary baseline contributes only a unit-modulus phase. The last inequality uses N>25/epsilon^2 and exp(1)<3. This contradicts(6). Hence, at EACH frequency t_h, some actual factor i_h satisfies

    |phi_(i_h)(t_h)|<epsilon.                           (11)

This rules out an arbitrary number of merely weak factors as the explanation of the small product: the controlling sum is the actual total pair loss B, not the word length.

## 6. Quantitative resonance separation identifies the actual factors

For one factor satisfying(11), write p=p_i, d=-log q_i and z=d/log h, where h is2 or3. The exact identity

    |phi_i(t_h)|^2
      =(1-2p)^2+4p(1-p)cos^2(pi z/2)

implies

    |p-1/2|<epsilon/2,
    |cos(pi z/2)|<2 epsilon,                            (12)

because4p(1-p)>1-epsilon^2>1/4. Our chosen epsilon is much smaller than1/40.

The mass bound(7) excludes q<=1/7. If q<=1/7, the event Z_i=1 makes X<=q<=1/7 regardless of every other factor and the ordinary baseline, so Pr(X<=1/7)>=p>(1-epsilon)/2>1/4, contradicting(7). Therefore d<log7. Since h>=2 and2^29>7^10,

    0<z=d/log h<log7/log2<29/10.                       (13)

There are no uncontrolled higher odd resonances. If2<=z<29/10, then

    |cos(pi z/2)|=sin(pi(3-z)/2)>=3-z>1/10,

using sin(pi u/2)>=u on[0,1]. This contradicts2epsilon<1/10. Thus0<z<2, where the same sine inequality gives

    |z-1|<=|cos(pi z/2)|<2epsilon.

Consequently

    |d-log h|<2epsilon log h<4epsilon,
    |q-1/h|<=|d-log h|<4epsilon=sigma/2.                (14)

The second step uses that x->exp(-x) has derivative magnitude at most1 on nonnegative arguments. Equations(12),(14) identify the selected factor inside the desired strict neighborhood of(1/2,1/h).

The selected factors at h=2 and h=3 are DISTINCT: their q neighborhoods have radius sigma/2<=1/200, whereas their centers differ by1/6. This conclusion does not assume independent selection or remove a factor before applying the second characteristic zero. Both extractions apply directly to the same complete word.

## 7. The remaining actual pair loss is uniformly small

Near either head, with both parameters within sigma<=1/100, f_1 stays above1/2. Both first partial derivatives of H_1 have magnitude at most2 there. Hence each selected factor's H_1 differs from its fair-head value by at most4sigma. The two endpoint head losses sum to log2.

Also, on m_1>2/5, the mean-value theorem gives

    |-log m_1-log2|<=(5/2)|m_1-1/2|<(5/2)delta.

Subtract the two actual selected head losses from the actual complete loss B. The result is exactly the nonnegative quantity in(1), and it is at most

    (5/2)delta+8sigma<=eta/4+eta/4<eta.                 (15)

All ordinary drift and EVERY other actual factor remain in that sum. The identified heads are within sigma of the desired pairs, hence within eta. This proves the assertion with the computable rational delta from(2).

## 8. Prior delta, original scope and effectivity limits

The rational exposing polynomial, fair endpoint and qualitative all-rival extraction are accepted providers from FOUR-SUPPORT-PERSISTENT-EXTRACTION.md. The addition proposed here is an explicit tolerance algorithm using exact characteristic zeros, an all-length loss-controlled product estimate, rational moment exposure/interpolation, and elementary resonance exclusion. It does not rely on a new measure compactness modulus or an unverified quantitative Khinchin theorem.

The actual word representation is the governing natural COMMON interface. Its application to calibrated original A/B rows uses the accepted all-core compiler, preserving one word for all supplied rows. This does not provide source-local extraction for arbitrary controlled/register or full C/D joint fibres, or for INDEPENDENT routing. Nor does it transfer to the old different-head killing fixture.

If this proof passes independent review, the previously qualitative extraction step in the fair-head killing theorem has a computable modulus. Completing an EFFECTIVE killing cutoff still requires explicitly bounded weak-cell quotient constants and an inverse-chart radius, or a proved terminating interval-bound construction for them. Their analyticity and local strictness suggest such bounds, but no final delta has been numerically evaluated and no particular rational NO instance is certified by this note. The tolerance formula may be far too conservative for practical execution; no efficiency claim is made.

Review gates: rational exposure positivity and interpolation constants; the entire50bound and product logarithm estimate; discontinuity near zero handled by mass splitting; the actual event implication X<=q_i; exact two frequencies and the29/10 resonance bound; distinct actual factors; and the remaining sum controlled by subtraction with no hidden-size premise.
