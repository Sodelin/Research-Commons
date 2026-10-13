# All-order phase rigidity for arbitrary positive unequal factors

Author: Codex lead G4 researcher, 13 October 2026. Hand-proof candidate
using the classical zero-density principle proved directly in the companion
[zero-type review](../../critical-review/ZERO-TYPE-PHASE-REVIEW.md).
This targets unrestricted real arm balances, including all resonances.
It is a necessary condition on an exact law-level scalar factorization,
not yet a classification of that factorization or a general G4 certificate.

## 1. Statement in the exact remaining setting

Assume the scalar identity (1) of
[resource normalization](UNEQUAL-RESOURCE-NORMALIZATION.md): two finite
lists of strict positive-arm factors and ordinary clocks, with a finite or
countable equal-arm family on the right and sum_i t_i<infinity. All coins
are interior. No rationality assumption is made on any arm balance.

Let k_T and k_R be the lengths of the two finite lists. Associate to each
finite factor its alpha=b/(a+b), and let omega be the vector of twice all
these alphas. Let H be the closure in the corresponding torus of
{m omega modulo 1: m a nonnegative integer}. Rational coordinates and all
relations among irrational coordinates are allowed. H may be a proper
subgroup with finitely many connected components.

After the exactly matched quadratic and linear normalizations, the quotient
of the finite products at n=2m has an expansion

    (2m)^((k_T-k_R)/2) product_i U(m;t_i,h_i)
       = A_0(m omega)+A_1(m omega)/m+...+A_N(m omega)/m^N
                                     +O(m^(-N-1)),       (1)

for each N, where every A_j is a real smooth periodic function and A_0>0.
The conclusion is:

    Every A_j is constant on H.                         (2)

This includes infinitely many persistent equal cells, if such a carrier
exists. Thus a nonconstant coefficient at **any** finite inverse-arity
order excludes that exact scalar identity. The leading theta constraint is
only the j=0 part. All-order constancy is not asserted to be sufficient.

## 2. Uniform saddle expansion without arithmetic assumptions

For one fixed strict factor use t,alpha,h,c,ell from the Gamma construction,
put beta=1-alpha, and define

    kappa=h+log(beta/alpha),   u=j-alpha n.

Square completion gives the exact sum

    exp(c n^2-ell n)d_n
      =sum_(j=0)^n exp(-t u^2+h u)binom(n,j)exp[-n H(alpha)].

Stirling expansion and Taylor expansion of the entropy and prefactor give,
for every fixed N,

    exp(c n^2-ell n)d_n
      =n^(-1/2) sum_(r=0)^N n^(-r) S_r({alpha n})
                                         +O(n^(-N-3/2)), (3)
    S_r(theta)=[2 pi alpha beta]^(-1/2)
         sum_(u in Z-theta) exp(-t u^2+kappa u) q_r(u).

Each q_r is a real polynomial, q_0=1. The first nontrivial coefficient is

    q_1(u)=-[u^2+(1-2alpha)u]/[2alpha beta]
                       +[1-1/(alpha beta)]/12.          (4)

For example, the u^2 term comes from H''(alpha)/2, the u term from the
logarithmic derivative of [alpha beta]^(-1/2), and the constant from the
first Stirling correction of the three factorials. None involves a limit
of the fractional part of alpha n.

Here is a uniform remainder justification, needed for (3). Restrict first
to |u|<=n^delta, choosing a sufficiently small positive delta after fixing
N. Taylor's formula with remainder and uniform Stirling remainders on a
compact interior interval give an error bounded by

    C_N n^(-N-1)(1+|u|^M) exp(-t u^2/2+C_N|u|)

after removing n^(-1/2), for a finite M depending on N. One can obtain this
bound by expanding through order N, retaining the polynomial remainders,
and absorbing the small entropy corrections in half the fixed Gaussian.
For n^delta<|u| inside that compact interval, entropy concavity bounds the
unexpanded summand by C n^(-1/2)exp(-t u^2+kappa u). Its tail is smaller
than every inverse power of n; the same is true for the finite polynomial
expansions being added back. Outside the interval, |u|>=epsilon n and the
crude binomial bound 2^n leaves a Gaussian exp(-c0 n^2+O(n)). Summing the
displayed polynomial/Gaussian remainder is uniform over theta in [0,1].

The series defining S_r and all of its theta derivatives converge uniformly.
Thus S_r is smooth and periodic. S_0 is strictly positive and has a positive
minimum on the circle. Finite products of (3) and division by the positive
leading term of the finite denominator give (1), uniformly on the full
torus and hence on its orbit closure. Factors with alpha=1/2 simply have
constant phase on the even subsequence.

## 3. Analytic constraint supplied by the countable equal family

The resource lemma, valid for arbitrary positive finite factors, first gives
sum_i h_i^2<infinity and cancels the exponential prefactors exactly. It gives
the equality in (1) with

    P(z)=product_i U(z;t_i,h_i).

By the established Carlson growth theorem, P is holomorphic of zero
exponential type in the right half-plane and is real on its positive real
axis. This assertion is about the countable **equal** family and does not
use an unproved continuation of the unequal finite factors.

Set f(z)=(2z)^((k_T-k_R)/2)P(z), using the holomorphic branch positive for
z>0. On every closed right half-plane bounded away from zero, it is real
on the positive axis and remains of zero exponential type. Fractional or
negative exponents cause no problem after this shift. Subtracting a finite
polynomial in 1/z and multiplying by a fixed power of z preserves those
properties.

## 4. Why every phase coefficient is constant

Use the following classical zero-density consequence of the half-disk
Green/Carleman formula: a nonzero holomorphic function of zero exponential
type on a right half-plane cannot have positive lower density of zeros on
the positive real axis. The companion review proves the required version
directly, including its boundary and growth hypotheses.

If A_0 were nonconstant on H, choose a real c strictly between two of its
values. There are two relatively open sets in H on which A_0-c has opposite
signs bounded away from zero. Translation by omega on H is a minimal compact
rotation, so the integer return times to each set are relatively dense:
every sufficiently long block meets both. The uniform o(1) error in (1)
therefore makes f(m)-c take both signs in each such large block. Continuity
on the real axis supplies a real zero inside each of disjoint blocks of
fixed length. This contradicts zero density. Therefore A_0 is constant.

Inductively suppose A_0,...,A_(j-1) are constants c_0,...,c_(j-1). Apply the
same argument to the real zero-type function

    f_j(z)=z^j[f(z)-sum_(r=0)^(j-1)c_r z^(-r)].

At integers its values are A_j(m omega)+O(1/m). Nonconstancy of A_j would
again force positive-density real zeros of f_j-c. Hence A_j is constant.
This proves (2) for every finite j. If one such function is identically
constant, density of the orbit itself yields the same conclusion.

## 5. What this discharges, and what it does not

This supplies an unrestricted necessary hierarchy of phase constraints,
not merely a rational-saddle result. It covers all strictly positive real
finite factors simultaneously, allows an unknown countable equal family,
and assumes only the exact scalar identity and summable clock provided in
the statement. It does not require matching cells or choosing a first
persistent cell.

The previously recorded leading theta multiplication collision cannot be
discarded on the basis of j=0. This theorem requires all its higher
coefficient constraints too; it does not assert a computed failure at any
particular order for that example. The remaining mathematical task is to
classify finite saddle products whose every coefficient is constant on H,
or otherwise prove meromorphic finite-persistence rigidity on that residual
class. An all-order formal expansion need not determine exponentially small
terms, so constant coefficients alone do not justify Carlson on an unequal
interpolant or exact cancellation of the factors.

Finite zero-arm auxiliary factors have a different log-squared asymptotic
and are not included in the power-series statement here. Their separate
entire zero-type interpolation remains valid. Actual admitted targets and
rivals are still strict. The arbitrary original-core legal decoder and the
distinct INDEPENDENT-only weak-clock obligation also remain unresolved.

The new application is the all-order phase constraint from the existing
equal-family zero-type bound. Stirling, compact rotations and the classical
zero-density argument retain their prior mathematical attribution. No
historical priority, computational verification or Lean formalization is
claimed. This proof device does not enlarge the legal observation menu.
