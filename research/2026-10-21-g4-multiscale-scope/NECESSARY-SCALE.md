# Necessary multiscale separation for bounded fair small-cell cap-six returns

21 October 2026. Contributor: dot (OpenAI), working with Nolan. Proof based on exact checked local identities; separate assistant-context scoped review PASS. Distinct from the sign-reversal example, which is NOT a return.

## Quantified statement

Fix an integer N>=1 and finite H>0. There are constants epsilon,c,C>0, depending only on N,H and the fixed forest coordinate norm, with this property.

Consider any word containing between 1 and N fair independently routed bigons, with strictly positive physical arms a_i+b_i and a_i-b_i (a_i>0, |b_i|<a_i), and positive ordinary connectors. Suppose its COMPLETE six-root forest kernel equals an ordinary kernel E_h, where 0<h<=H. Put

    A=max_i a_i, z_i=b_i^2, S=sum_i a_i^3, Z=sum_i z_i.

If A<epsilon, then some cell j satisfies

    c A^(3/2) <= |b_j| <= a_j <= C A^(3/2).

Thus every bounded-cell sequence of such exact returns with all means tending to zero must contain a cell whose mean and imbalance are both comparable to the three-halves power of its largest mean. In particular there is no such sequence with max_i |b_i|/a_i tending to zero. There is also no such sequence with min_i a_i/A^(3/2) tending to infinity.

The quantifiers allow arbitrary positive placement gaps, including gaps tending to zero, arbitrary unequal rates of cell shrinkage, nonanalytic dependence and Puiseux parametrizations. They do not allow N to grow without bound, H to diverge, nonfair routing, or a cell mean bounded away from zero. No existence is asserted at the necessary scale.

## 1. Uniform analytic source estimates

All estimates below are on a finite-dimensional complete-forest representation, uniformly for 0<=p<=H, 0<a<=epsilon, and 0<=z<a^2. Constants are independent of the particular word.

The fair-cell matrix B(a,z), pair survival and normalized cell J(a,z)=B exp(-h(a,z)Q) are analytic near (a,z)=(0,0). This follows by averaging the two arm assignments: only even powers of the half-difference b survive. The logarithm defining h=-log q2 is analytic near q2=1. Analytic continuation at formal z<0 does not represent a physical source.

The matrix J-I has no pure-a terms of degree one or two. Its first relevant terms are

    a^3 U3/8 + z V3,
    a^4 U4/16 + az V4/2,
    a^5 U5/32 + a^2z V5/4.

Therefore, in a fixed matrix norm,

    ||J-I|| <= C(a^3+z).                                      (1)

Let ell=P[:,14] be the exact covector of the published positive-base obstruction. Its checked transport identities annihilate U3,V3,U4,V4,U5 for every p and give

    v0 Ad_p(V5) ell=exp(-9p).

Analytic Taylor division, with these identities, gives the stronger scalar estimate

    v0 Ad_p(J-I) ell
      = exp(-9p) a^2 z/4 + R(a,z,p),
    |R(a,z,p)| <= C(a^6+a^3z+z^2).                           (2)

Indeed the omitted pure-a monomials are divisible by a^6, the remaining monomials linear in z by a^3z, and all terms of degree at least two in z by z^2. Their analytic coefficient functions are bounded on a sufficiently small closed neighborhood and the compact placement interval. This is a uniform analytic remainder estimate, not a claim inferred from a finite numerical sample.

## 2. Necessary exact scalar balance

For the actual fair source,

    q2=(1+e^(-a)cosh b)/2,
    q3=(e^(-3a)cosh(3b)+3e^(-a)cosh b)/4.

The scalar K3=log q3-3log q2 has expansion

    K3=-a^3/8+3z/4+O(a^4+az+z^2).                          (3)

Ordinary connectors contribute zero to K3. Exact full-six equality implies exact lower-root diagonal equality, hence sum_i K3_i=0. Since a_i<=A and z_i<a_i^2<=A^2,

    |-S/8+3Z/4| <= C A(S+Z).                               (4)

For sufficiently small A, the Z error is absorbed into the positive 3Z/4 coefficient. Consequently

    Z=S/6+O(A S),                                           (5)

and in particular c0 S<=Z<=C0 S for fixed positive constants. Since A^3<=S<=N A^3, this also forces Z comparable to A^3. This step excludes the all-equal-arm boundary without assuming any individual balance between z_i and a_i^3.

## 3. Chronological product and uniform remainder

Let h_i=-log q2(B_i)>0 and let s_i be the cumulative ordinary connector hazard preceding cell i. Exact pair calibration gives sum of ordinary hazards plus sum_i h_i = h<=H. Thus every normalized chronological placement

    p_i=s_i+sum_(j<i)h_j

lies in [0,H]. The exact identity is

    W E_(-h)=product_i Ad_(p_i)(J_i),

in original order. There is no physical negative-duration edge. Put D_i=Ad_(p_i)(J_i-I). Equation (1) implies sum||D_i||<=C(S+Z). The finite product expansion and smallness give

    ||product_i(I+D_i)-I-sum_iD_i|| <= C(S+Z)^2.             (6)

This bound retains ALL ordered cross terms; it does not assume they vanish or commute. Apply v0 and ell, use (2), and set

    T=sum_i exp(-9p_i) a_i^2 z_i.

Exact F=0 implies

    T/4 <= C[sum_i a_i^6 + sum_i a_i^3 z_i
              + sum_i z_i^2 + (S+Z)^2].                    (7)

Using (5), S<=N A^3, sum a_i^6<=A^3 S, sum a_i^3z_i<=A^3 Z and sum z_i^2<=Z^2, the right side is bounded by C A^3 S. Since exp(-9p_i)>=exp(-9H)>0,

    sum_i a_i^2 z_i <= C A^3 S.                            (8)

No sign is assigned to the remainder or to the chronological cross products; only their magnitude is bounded.

## 4. Extracting the necessary asymmetric small cell

Choose j with z_j=max_i z_i. Since the number of cells is at most N,

    z_j >= Z/N >= c0 S/N >= c1 A^3.

Equation (8) gives

    a_j^2 z_j <= C A^3 S,
    a_j^2 <= C N A^3 S/Z <= C1 A^3.

Physical positivity gives z_j<a_j^2. Combining these inequalities yields

    sqrt(c1) A^(3/2) <= |b_j| < a_j <= sqrt(C1) A^(3/2),

which proves the stated conclusion. In particular |b_j|/a_j is bounded below by a positive constant depending only on N,H.

## 5. Limits and comparison with the checked example

The separate two-cell sign-reversal construction has a1=tau^2, a2=tau^3/2 and |b2|~tau^3/sqrt(6). It reaches exactly the scale where this theorem permits a possible escape. It is not a full return and therefore does not prove sharpness as an existence theorem. It does demonstrate that the original covector can change sign at this scale, so extending its simple positive-leading-term argument without the competing terms is invalid.

The accepted cap-five suppliers do not assert vanishing of this sixth-root covector; the accepted review explicitly retains a sixth defect. No contradiction or replacement of those results is claimed.

This is a necessary condition for bounded-N, all-small, fair returns, not a maximal classification of all positive serial words. The G4 fixed-target/all-finite-panels master quantifiers remain open. Large/nonordinary cells, growing N, other routing probabilities and more general architectures are outside the result. No new positive ordinary zero, Jacobian, uniform-exposure return construction or finite forcing panel is supplied.

## Evidence and verification boundary

The finite source identities use the original complete labelled-forest generator and pinned projection from the earlier checkpoint. EVIDENCE.md identifies local checks and distinguishes them from the hand proof of uniform estimates and quantified scale separation. This result does not follow from the sign-reversal example alone.
