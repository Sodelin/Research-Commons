# Single-zero-arm auxiliary endpoints of the mixed reference comb

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived argument under review.**
No computation or formal verification is asserted. These are auxiliary
compactification factors, not newly admitted physical sources or rivals.

The physical reference-comb formula and strict mixed continuation are in
[MIXED-COMB-FIXED-PHASE-LAPLACE.md](MIXED-COMB-FIXED-PHASE-LAPLACE.md).
Retain its ordinary internal length T>0 and coin 0<g<1; write q=1-g,
lambda_l=l(l-1)/2, and

    Q_(j,l)=(-1)^(l-j)(2l-1)
                  Gamma(j+l-1)/[Gamma(j)Gamma(l-j+1)].

## 1. Zero early arm: a=0, b>0

Let r count A roots sent to the late arm. The exact integer formula gives

    v_n/kappa_(n+1)=g^n E_early(n),

    E_early(z)=sum_(r>=0) sum_(l>=1) sum_(j=1)^l
       (q/g)^r exp(-b lambda_r-lambda_l T) Q_(j,l)
       * R_(r,l)(z)/[Gamma(r+1)Gamma(r+j+1)],            (1)

    R_(r,l)(z)=Gamma(z+1)Gamma(z+2)
                  /[Gamma(z-r+2-l)Gamma(z-r+1+l)].

The integer truncation is exact: when r>n or l>n-r+1 the first reciprocal
Gamma in R vanishes. The surviving terms reproduce the finite physical
formula. In particular E_early(0)=1.

A useful exact simplification is

    R_(r,l)(z)=(z)_(fall r+l-1)
        * (z+1)_(fall r+1-l),                    if l<=r+1,

    R_(r,l)(z)=(z)_(fall r+l-1)
        / (z+2)_(rise l-r-1),                    if l>r+1.         (2)

Empty products are one. Thus the only possible poles of an individual
summand are simple poles at -2,-3,... . On Re z>=0, recurrence-factor
bounds give, with N=1+r+l,

    |R_(r,l)(z)|
       <=exp[C N log(2+N)](1+|z|)^(2r).                (3)

Indeed every numerator factor is at most C(1+N)(1+|z|), whereas a denominator
factor |z+2+i| is at least c(1+|z|+i). The numerator degree minus denominator
degree is exactly 2r in both cases. This cancellation is necessary: a bound
with an uncancelled power |z|^(2l) would not establish the desired result.

The spectral prefactor satisfies |Q_(j,l)|<=exp[C l log(2+l)], and the two
constant Gamma denominators in (1) are at least one. Hence the strict
Gaussian factors in r and l dominate all index-only growth. More precisely,
for L=log(2+|z|), absorb C N log(2+N) and the linear routing exponent into
small multiples of r^2+l^2, leaving a bound of the form

    sum_(r,l>=0) C exp(-c_b r^2-c_T l^2+2rL)
       <=C' exp(C' L^2).

The finite j sum contributes at most l. Therefore (1) converges normally
on the closed right half-plane and

    |E_early(z)|<=C exp[C log^2(2+|z|)], Re z>=0.        (4)

In particular it is holomorphic of zero exponential type there and real
on the positive real axis.

The same series is normally convergent on each compact subset of the
plane away from -2,-3,... . For fixed compact z sets, the numerator product
in (2) is bounded by exp(C_K N log(2+N)); the nonvanishing denominator factors
are bounded below uniformly for finitely many early factors and grow at
least linearly for the remaining factors. Gaussian domination applies
again. Near a fixed negative integer -m, multiplying every term by z+m
removes its possible simple pole; the same compact estimates hold uniformly
in all indices. Thus E_early is meromorphic on the plane with at most simple
poles at -2,-3,... and no other poles. It is not asserted to be entire.

Finally, the event that all n A roots choose the zero early arm has routing
weight g^n. On this event the C_(n,n) factor is one, and there are no lower
arm mergers to suppress. Its contribution alone gives

    E_early(n)>=1, n=0,1,2,... .                       (5)

Together with (4), this yields log E_early(n)=O(log^2(2+n))=o(n). The endpoint
therefore has one ordinary linear exponential factor g^n and a zero-type remainder that is positive
at every nonnegative integer; no inverse-power expansion of E is
claimed or needed.

## 2. Zero late arm: b=0, a>0

Now let r count A roots sent to the early arm. The exact formula becomes

    v_n/kappa_(n+1)=q^n E_late(n),

    E_late(z)=sum_(r>=0) sum_(l=1)^(r+1) sum_(j=1)^l
       (g/q)^r exp(-a lambda_r-lambda_l T) Q_(j,l)
       * P_(r,j)(z)/[Gamma(r+2-l)Gamma(r+1+l)],         (6)

    P_(r,j)(z)=Gamma(z+1)Gamma(z+2)
                    /[Gamma(z-r+1)Gamma(z-r+j+1)]
              =(z)_(fall r)(z+1)_(fall r+1-j).         (7)

The cutoff l<=r+1 holds identically, because Gamma(r+2-l)^(-1) is zero
outside that range. Consequently j<=r+1 and both products in (7) are
polynomials. Their degree is 2r+1-j<=2r. At integer n the first product
vanishes for r>n, so the finite physical formula is recovered exactly.

Uniformly on the whole complex plane,

    |P_(r,j)(z)|<=exp[C r log(2+r)](1+|z|)^(2r).

The constant Gamma denominators in (6) are positive factorials and at least
one. Since l,j<=r+1, their spectral prefactor and the number of terms are
absorbed by exp[C r log(2+r)], while the Gaussian exp(-a lambda_r) remains.
The same square-completion bound as before gives normal convergence on
all compact sets and

    |E_late(z)|<=C exp[C log^2(2+|z|)], z in C.          (8)

Thus E_late is entire of zero exponential type. It satisfies E_late(0)=1.
The event that all A roots choose the zero late arm contributes q^n,
since C_(n,0)=1. Hence E_late(n)>=1 at every nonnegative integer, and
log E_late(n)=O(log^2(2+n))=o(n).

## 3. The common T=0 boundary

If T=0, no merger occurs on the mixed internal edge, so C_(n,k)=1 exactly.
The normalized comb then reduces to the previously established private
cell diagonal. Strict arms use its fixed-phase Gamma interpolation;
a single zero arm uses its reviewed endpoint entire series. If both arms
and T vanish, the normalized comb is identically one. These are direct
finite physical identities, not limits obtained by interchanging the
spectral sum at T=0.

## 4. Why these endpoint factors fit the phase argument

A finite product of E_early and E_late factors is holomorphic of zero
exponential type on the right half-plane, positive at nonnegative integers,
meromorphic with finite-order poles on the plane, and equal to one at zero.
Its integer logarithm is o(n). These are precisely the properties used by
the weighted phase-sign argument and final Carlson multiplier step in
[UNIFORM-LAPLACE-PHASE-REMOVAL.md](../../chronology/continuation-2110z/UNIFORM-LAPLACE-PHASE-REMOVAL.md),
Section 7. Entire continuation was stronger than that proof required;
finite-order left-half-plane poles are harmless.

Accordingly, whenever a legitimate exact scalar identity contains finitely
many such endpoint factors, they may be retained as E_T and E_R rather
than divided out on a complex domain. Their o(n) logarithms do not alter
the quadratic or linear resource limits. Their positive values preserve
the signs in the phase-coefficient induction. After exact phase removal,
their zero-type bounds permit Carlson, and their finite pole orders cannot
hide an accumulating sequence of off-pole zeros. This is a conditional
analytic compatibility statement, not a new source-extraction theorem.

## 5. Both arms zero with T>0: unresolved here

When a=b=0 and T>0, the Gaussian in r disappears. Neither proof above then
supplies a summable uniform majorant or a zero-type remainder after merely
factoring g^n or q^n. In fact the summand's binomial-square structure suggests
a different exponential rate and a saddle of width sqrt(n), rather than
the fixed-width Gaussian of the strict mixed-arm case. That change cannot
be ignored or treated by an unexplained endpoint limit.

This packet does not establish whether such a core boundary is excluded
by the retained COMMON profile constraints. Positive total displayed
branch lengths alone do not visibly exclude zero lengths in a chosen
opened-core decomposition, because finite private-word clocks can supply
part of those totals. A correct exclusion needs the actual source geometry
and its precise decomposition. Otherwise a separate phase-free continuation
for the both-zero-arm mixed factor is required.

The full original G4 legal observation bridge, finite mixtures of different
quadratic or linear rates, and arbitrary-source forcing remain separate
obligations. No fixed-target impossibility result is asserted. All arguments
above are hand proofs using the already attributed pure-death formula and
elementary Gamma recurrences; no historical novelty or Lean verification
is claimed.
