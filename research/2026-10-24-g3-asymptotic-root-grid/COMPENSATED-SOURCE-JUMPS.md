# Uniform actual-source bounds for compensated commutator jumps

Stable key G3-COMPENSATED-SOURCE-JUMPS-01. Existing G3 owner,24October2026.
**PROVED BY HAND at the scope below**, author self-review complete.
Independent correctness review and Lean are absent. No source/coefficient
producer, numerical/symbolic control, solver, model/native/compiler or old
suite was run. This is a derived source-estimate component of the existing
conditional full-scope G3 attempt, not a new full attack or an index theorem.

## 1. Actual source scope and statement

Work in the OLD actual multiplicative9/7/6/4 forest representation,
with ordinary generator diag(-36,-21,-15,-6) and kappa=5/3.
The input roots are CURRENT tokens; pre-existing trees are grafted opaque.
This is not an arbitrary full Code/population/register matrix.

For one genuine equal-arm INDEPENDENT cell put

    q=exp(-u), 0<u<=log2, 0<g<1,
    v=g(1-g), beta=(2g-1)^2,
    Z=q+2v(1-q), tau=-log Z,
    C=exp(-tau Q) B_I(q,q,g),
    r=v*(beta*u^2+u^3),
    s=v*(beta^2*u^3+beta*u^4+u^5).                 (1)

Q denotes the ordinary generator, not a new physical control. The inverse
in C is algebraic normalization; B=exp(tau Q) C is the SAME actual cell.

Write its represented normalized matrix as

    C=[ d1 F F 0 ]
      [ 0 d2 0 -kappa*F+sigma ]
      [ 0 0 d3  kappa*F+rho   ]
      [ 0 0 0 d4 ].

There is a fixed effective constant C0 such that, for ALL the above coins
and scales,

    max_j |dj-1|+|F| <= C0*r,
    |rho|+|sigma| <= C0*s,
    d1>=2^(-36).                                  (2)

Constants do not require a coin margin. Endpoint coins are used ONLY for
finite polynomial identities/bounds; actual source coins remain strict.

Use the EXACT eigenbasis P_h of the unchanged active reference

    S(t)=E(t) B_I(t/(2-t),t/(2-t),1/2) E(t^2*(2-t)),
    h=-log t,

as in FORMAL-AFFINE-STORAGE.md. Its entries are denoted A,B,D,E,G:

    P_h=[ 1 A B G ]
        [ 0 1 0 D ]
        [ 0 0 1 E ]
        [ 0 0 0 1 ].

They depend only on the known reference, not on the unknown word.
A,B,D,E=O(h^2), G=O(h^4). On normalized first-row coordinates a,b,z define

    La=-D-kappa*A+2*kappa*B,
    Lb=-E-kappa*B,
    Xi=z-(kappa/2)*(b^2-a^2)+La*a+Lb*b.            (3)

For all sufficiently small h>0, every actual normalized cell append in
this basis satisfies

    Xi+ = (d4/d1)*Xi- + eps,

    |eps| <= C1*[
       r*(a^2+b^2)
       +(s+h^2*r)*(|a|+|b|)
       +h^4*r+h^2*s ].                            (4)

The bound is evaluated at the entering a,b. It is uniform in all actual
coins, arbitrary relative cell scales and all finite word counts.
It does not assume that eps has one sign.

During each ordinary interval the EXACT drift is

    Xi'-30Xi = -6*kappa*b^2
                +30*kappa*B*(b-a)+Theta(h),

    Theta=eta-30*kappa*A*B+70*kappa*B^2
         =O(h^6).                                (5)

The previous eta=-4*h^4/76545+O(h^5) remains valid. Equation(5) is the
drift of the DIFFERENT, explicitly compensated storage Xi.

## 2. Prior source comparison: reuse the completed coefficients

The source representation, finite EPPF polynomials, projectivity/grafting,
source pair formula, fair two-jet identity and generic affine jump formula
are OLD/PROVED. This note does not rederive or execute their coefficients.

At Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6, COMPLETE proof,
README and later scoped HAND ACCEPT bodies were read and hash matched:

* research/2026-10-08-dot-g4-biased-transverse-source-1225z/
  BIASED-COIN-ORDER-NINE-TRANSVERSE-CANDIDATE.md,
  11823B/SHA5c53dd3c1fd2392f6abfccccfbea925f8876d3d3a60cc6be4d09e7d4ed3fdd6e,
  blob08f7e1036e422c4cedac85cf09ed295e70b6bf1c.
  Its review7977B/SHA6b8e81add351da0d8170828d6f47b591da1fa7a7bdb519f33e57542566037c0b
  accepts the disclosed source identities at scope.
* research/2026-10-08-dot-g4-interior-coin-source-jets-1213z/
  INTERIOR-COIN-SOURCE-JETS-ADDENDUM-CANDIDATE.md,
  7641B/SHA81de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6;
  review6182B/SHAf659f795f963fc9c923f6427e06bb52d905dd8be211582f72387212f03c82f83.

The preserved candidate headers do not reopen these later accepted results.
The exact homogeneous cubic combinations and the fair fourth-order
cancellation are reused below.

The later G4 R9 proof9036B/SHAd4352b1663f823594ffa797c8e401f1302daf185f988b6b12e6232b0b64d2781
was also read COMPLETE. Its near-fair no-return theorem retains its OWN
coin-window and ordinary-endpoint assumptions. We do not extend it here.

The immediate G3 predecessor is the8059B generic affine/reference note,
SHA961a9644e9d6e88a888dfa4e0acd02e21e285e11c703fe2ad8ad5dde2080b025,
published at980c2d0ebb682a593548541f172a1e12bce6b7b4. It supplies P_h,
the complete jump algebra and the original forced drift, but no estimate(4).
The additional work is the global equal-arm polynomial factorization and
the reference-dependent horizontal compensation. Historical novelty is
not claimed. Relevant current/archive aliases were compared before this write.

## 3. Polynomial factors give constants uniform at rare coins

Let f0,H0,U0=-H0+2e0 be the actual B entries. These and each no-merger
diagonal b_n(q,g) are rational polynomials in q,g. At either deterministic
coin endpoint the cell is ordinary, so f0=H0=e0=0 and b_n=Z^lambda_n.
Every corresponding difference is therefore divisible by v=g(1-g).

The OLD pair-normalization/two-jet argument gives the exact finite
polynomial divisibility

    b_n-Z^lambda_n
       =v*(1-q)^2*[beta*An(g)+(1-q)*Bn(q,g)],
    f0 =v*(1-q)^2*[beta*Af(g)+(1-q)*Bf(q,g)].       (6)

Here and below the lettered polynomials have rational coefficients and
are not independent source actuators. One can compute them by finite
division of the retained source polynomials. First-order cancellation
holds for every coin; fair second-order cancellation and g<->1-g
symmetry supply beta. No numerical extrapolation is used.

Define the EXACT polynomial transverse numerators

    NT=Z^21*H0-kappa*f0,
    NU=Z^15*U0+kappa*f0.                           (7)

Their denominators in rho,sigma are both Z^36. To obtain their factors,
reuse the OLD homogeneous source variables

    mu=(g^2+(1-g)^2)*u,
    delta=(2g-1)*u,
    variance=v*delta^2, third=v*(1-2g)*delta^3
                                      =-v*beta^2*u^3.

The exact cubic combinations in the accepted biased-source proof,
followed by its nominal exp(-mu Q) normalization, give

    rho_nominal=-2*third+terms of total degree>=4,
    sigma_nominal=third+terms of total degree>=4.

Indeed its exact degree-three A9-A6 and e terms are
63*mu*variance+18*third and -mu*variance-third/2. The normalization
corrections cancel mu*variance. Thus no balanced/parabolic restriction
has been added to this homogeneous degree-three identity.

Actual tau=mu+O(u^2). Since f0=O(u^2), replacing nominal mu by tau
changes the transverse expressions only at order>=4. Consequently

    [u^3]rho=2v*beta^2, [u^3]sigma=-v*beta^2,
    all lower coefficients vanish.                 (8)

At the fair coin f0=O(u^3) and tau-mu=O(u^2), so the normalization
change starts only at order5. The accepted fair specialization gives
rho_nominal,sigma_nominal=O(u^5): its O(epsilon^9) estimate on
u=2epsilon^2 is even in epsilon. Thus the actual fair transverse
polynomials have zero degree-four coefficient too.

Put d=1-q. Since u=d+O(d^2), the cubic coefficients in(8) are unchanged.
Each quartic coefficient is symmetric in g and vanishes at g=1/2, so
it is divisible by beta. The exact endpoint factor v already holds.
Hence finite polynomial division gives EXACTLY

    NT=v*d^3*[ 2*beta^2+d*beta*PT(g)+d^2*RT(q,g)],
    NU=v*d^3*[-beta^2+d*beta*PU(g)+d^2*RU(q,g)].     (9)

This is an identity of actual source polynomials. Although the reused
jets were proved on compact interior coin sets, their coefficient
equalities are polynomial identities on a nonempty open interval.
Equation(9), not an assumption of uniform analytic continuation, extends
them to the entire closed coin interval.

On q in[1/2,1],g in[0,1], Z>=q>=1/2. Rational coefficient L1 bounds
for(6),(9), division by the positive powers of Z and d<=u prove(2).
All constants are effective finite coefficient bounds; no solver or
source evaluation is needed to define them.

We will also use the elementary consequence, for u<=1,

    r^2/s
      =v*u*(beta+u)^2/(beta^2+beta*u+u^2)
      <=2v*u<=1/2,

so r^2<=s/2. Actual r,s are positive; the boundary case is interpreted
by continuity for bounds only.

## 4. Exact conjugation and cancellation of the large jump constant

Write the off-diagonal entries of P_h^-1 C P_h as X,Y,V,U,T.
Direct triangular multiplication gives EXACTLY

    X=F+A*(d1-d2), Y=F+B*(d1-d3),
    U=-kappa*F+sigma+D*(d2-d4),
    T= kappa*F+rho+E*(d3-d4),

    V=G*(d1-d4)+A*D*(d4-d2)+B*E*(d4-d3)
       +[D+E+kappa*(A-B)]*F-A*sigma-B*rho.          (10)

No central term is omitted. In particular X and Y generally differ.

Use the already proved generic affine jump identity with La,Lb in(3).
Its quadratic coefficients are O(r), and its two linear coefficients
are O(s+h^2*r+r^2)=O(s+h^2*r), using(2) and r^2<=s/2.
The apparent leading F terms in U+kappa*X and T-kappa*Y cancel;
the remaining changes include every diagonal and affine correction.

For completeness, its constant numerator is

    d1*[V+La*X+Lb*Y]-(kappa/2)*(Y^2-X^2).           (11)

The coefficient of F in the FIRST bracket vanishes EXACTLY because

    La+Lb= -[D+E+kappa*(A-B)].                     (12)

All remaining terms in that bracket are O(h^4*r+h^2*s):
G,AD,BE,La*A,Lb*B are O(h^4), and A*sigma+B*rho is O(h^2*s).
Also Y-X=O(h^2*r), X+Y=O(r), hence
Y^2-X^2=O(h^2*r^2)=O(h^2*s). Division by d1^2 is bounded.
This proves the full estimate(4), without a coin margin or a word-count
constant. It is a bound on one SAME actual cell and its retained source
entries, not independent fitting of matrix coordinates.

Equivalently the compensator is the FIXED combination

    Xi=Phi+2*kappa*B*a-(10*kappa/3)*B*b,

of the former storage and horizontal coordinates. It adds no observable.

## 5. Forced drift and the order-six reference residual

Reuse q12=-15A,q13=-21B and the original affine identity
Phi'-30Phi=-6*kappa*b^2+eta. Applying the ordinary derivative to the
two added linear terms gives EXACTLY(5), with

    Theta=eta-30*kappa*A*B+70*kappa*B^2.            (13)

There is a short source-faithful proof of Theta=O(h^6), avoiding any
new high-order coefficient producer. Apply the exact identities to the
KNOWN one-cell reference S(t) itself, not to an unknown word.

Its actual pair clock is3h. The normalized source has r=O(h^3),s=O(h^5).
Along its finitely many ordinary intervals, all of length O(h),
a,b=O(h^3): q12,q13=O(h^2) and the single injection is O(h^3).
Moreover b-a=O(h^4). Its ordinary forcing difference
q13-q12=O(h^3) by the previously proved leading eigenvectors;
the jump difference Y-X=O(h^5) and the other difference increments
are O(h^6). These bounds hold across the single actual source cell.

A positive integrating factor for Xi has w'= -30w and
w+=w-*(d1/d4), so w stays bounded and its integral is >=c*h.
Both endpoint Xi values are zero, because P_h EXACTLY diagonalizes S.
Estimate(4) gives eps=O(h^7). The integrated b^2 and B*(b-a) terms
are also O(h^7). Therefore

    |Theta|*integral(w) <= C*h^7,
    |Theta|<=C*h^6.

This proves the claimed cancellation of the reference orders below six.
No sign or exact leading order-six coefficient is asserted. The former
eta order-four term has not been dropped; it is explicitly compensated
by(13). Constants can be made effective from the retained rational-in-t
source/eigenvector formulas after their removable zeros at t=1 are
cancelled. No new source or physical inverse is constructed.

## 6. The exact all-length balance and what it does NOT prove

Let K be ANY actual finite strict equal-arm word on the active paired
fibre, COMMON E(c), I pair c^(3/4), c=2^(-1/m), and suppose its full
forest operators commute with S(t) through at least the existing nine-root
carrier. Its coins, scales, finite count and higher diagonals are unknown.

Factor EACH actual cell in its ORIGINAL position as exp(tau_i Q) C_i.
All ordinary intervals remain positive and the total nominal clock is

    Tnom=sum physical ordinary times+sum tau_i
        =-log b2I(K)=3H/4, H=-log c.                (14)

This is the mathematical pair normalization of the actual word, not an
input calendar relation or identification of H with its bare ordinary
time. The latter can be different. For reference, tau_i>=3u_i/8 when
u_i<=1, from tau_i>=u_i/2-log cosh(u_i/2) and log cosh x<=x^2/2.

In the exact reference basis a,b,z start and end at zero: the commuting
represented whole matrix is diagonal, with its UNKNOWN actual diagonals.
Consequently the finite chronological balance is

    6*kappa*integral w*b^2
      =30*kappa*B*integral w*(b-a)
         +Theta*integral w+sum_i w_i+*eps_i.         (15)

Every eps_i obeys(4). The integrating factor is uniformly positive:
it equals the ratio of the current nine-/four-root no-merger diagonals,
so c^36<=w<=1 at every nominal prefix. After a completed C jump the
prefix is the actual source prefix; inside its preceding ordinary
interval it is an actual positive prefix followed by an ordinary
interval of duration at most the remaining arm budget. The OLD
source/deletion diagonal bounds therefore apply. No norm of an arbitrary
signed standalone C operator is being called stochastic.

All equations preserve the original chronological order, current-root
routing, opaque grafts and same natural physical tuple. COMMON is not
refreshed. The statement is a necessary selected representation of the
full forest commutator, not its converse.

Bounds(2),(4), the effective source factors, compensation, residual(5)
and exact all-length balance(15) are completed. The remaining source
problem is to control the SIGNED chronological cancellation in(15)
and the b-a term sufficiently to force the inferred index. An absolute
sum of error bounds is not a coercivity proof. In particular none of
these results supplies V_h<=C*h^5, a finite positive source selector,
AG-Pair, a bound on unknown word size or original terminating NO.

Original G3 stays ACTIVE/UNRESOLVED. This note creates no new master
requirement, extra proof/review/compile gate, source observer, physical
actuator, cap ladder or independently fitted response row. Existing next
action: extract actual source coercivity/index information from(15), or
a materially superseding actual source disproof, with all original
quantifiers retained. All owners, no-local-Git/no-agent and existing
model/native/controller/held/USED/UNKNOWN/privacy restrictions persist.
