# Unequal-arm continuation by centered Gamma ratios

Author: Codex lead G4 researcher, 13 October 2026. Hand-derived argument;
the delegated Sol 6.1 checker independently checked the formulas and growth
estimates in [its audit](RATIONAL-INTERPOLATION-SOL-AUDIT.md).
The numerical fixtures in that audit are separate evidence. No Lean proof.

This replaces the earlier moving-log-odds encoding on an exact arithmetic
subsequence. It proves a new conditional analytic bridge; it does not restrict
the original admitted parameters or prove general G4. In particular, rational
balance of the finite *rival* factors is not implied by a rational target.

## 1. Exact statement

For positive arm exposures a,b and an interior routing coin g, let

    d_n = sum_(j=0)^n binom(n,j) g^j (1-g)^(n-j)
                exp[-a j(j-1)/2-b(n-j)(n-j-1)/2].           (1)

Put

    t=(a+b)/2,  alpha=b/(a+b),
    h=log(g/(1-g))+(a-b)/2,
    c=ab/[2(a+b)],
    D=alpha log(alpha/g)+(1-alpha)log((1-alpha)/(1-g)),
    ell=2c-D.

Suppose alpha=P/Q with coprime integers 0<P<Q, and write B=Q-P. There is a
bounded holomorphic F on Re z>=0, meromorphic on the complex plane, such that

    d_(Qm)=exp[-c(Qm)^2+ell Qm] F(m),  m=0,1,... .         (2)

Here bounded holomorphic on the closed half-plane means holomorphic in its
interior with continuous boundary values. Its possible poles are simple and
belong to {-r/Q:r positive integer, Q does not divide r}. In particular it
has zero exponential type in the right half-plane and F(0)=1.

## 2. Construction and integer identity

Let H(alpha)=-alpha log alpha-(1-alpha)log(1-alpha), and set

    R_s(z)=Gamma(Pz+1)Gamma(Bz+1)
                 /[Gamma(Pz+s+1)Gamma(Bz-s+1)],
    G(z)=sum_(s in Z) exp(-t s^2+h s) R_s(z),
    C(z)=Gamma(Qz+1)/[Gamma(Pz+1)Gamma(Bz+1)]
                 exp[-Q H(alpha)z],
    F(z)=C(z)G(z).                                      (3)

The Gamma ratios R_s are rational functions, continued at removable points.
For nonnegative integer m, binom(Qm,Pm)R_s(m)=binom(Qm,Pm+s), with the
right side zero outside its usual finite range. Completing the square in
(1) at j=Pm+s gives

    d_(Qm)=exp[-c(Qm)^2+L Qm]
               sum_s exp(-t s^2+h s) binom(Qm,Pm+s),
    L=b/2+log(1-g)+alpha h.

The identity L+H(alpha)=2c-D=ell proves (2), including m=0.

## 3. Bounded growth: the missing property of the earlier encoding

For s>=1 and r>=1, integer Gamma shifts give

    R_s(z)=product_(k=0)^(s-1) (Bz-k)/(Pz+k+1),
    R_(-r)(z)=product_(k=0)^(r-1) (Pz-k)/(Bz+k+1).        (4)

For Re z>=0 each factor in the first expression is bounded by max(B/P,1),
and each in the second by max(P/B,1). This follows by squaring moduli:
the denominator's nonnegative cross term dominates the numerator's negative
one, and the remaining quadratic and constant terms obey the stated bound.
Writing M=max(B/P,P/B,1),

    |G(z)| <= sum_(s in Z) exp[-t s^2+(|h|+log M)|s|]<infinity.  (5)

Thus G is bounded and its defining series converges normally there. Uniform
Stirling asymptotics in the closed right half-plane give

    C(z)=sqrt[Q/(2 pi P B)] z^(-1/2)(1+O(1/|z|)).         (6)

All exponential factors cancel because Q H(alpha)=Q log Q-P log P-B log B.
The error is uniform, including the imaginary boundary directions. C is
also continuous and has no poles on the bounded part of the closed right
half-plane, hence is bounded throughout. Equations (5)-(6) prove the asserted
growth of F. The parameters t and h stay fixed as z varies.

## 4. Meromorphic continuation

The only possible poles of R_s lie in

    Lattice = {-r/P:r>=1} union {-r/B:r>=1}.

On a compact set disjoint from this lattice the individual factors in (4)
are bounded by a constant depending on that compact set, uniformly in k:
as k tends to infinity their moduli tend uniformly to one. Thus
|R_s(z)|<=C_K^|s|. The Gaussian in (3) gives normal convergence of G there.
Near one lattice point z0, at most one denominator factor in each R_s has
a zero. Multiplication by z-z0 removes it, with the same exponential-in-|s|
bound. Consequently G has at most simple poles at the lattice points.

C has a simple zero at every such point. At a negative integer its numerator
has one simple Gamma pole and both denominator Gamma factors have one; at
a lattice point that is not an integer just one denominator Gamma factor
has a pole. Coprimality of P,Q shows the numerator is regular there. These
zeros cancel all possible poles of G. C itself can have simple poles only
at -r/Q with Q not dividing r; G is regular there. This proves the claimed
meromorphic continuation of F. Removable cancellations may shrink its pole
set further and do not affect the argument.

For a=b, take P=1,Q=2. Then c=t/4 and ell=t/2-log cosh(h/2).
At the nonnegative integers F agrees with the inherited U(z;t,h). Both are
bounded in the right half-plane, so Carlson uniqueness gives F=U. This is a
consistency check, not a new proof of the equal-arm theorem.

## 5. Finite meromorphic factors cannot hide infinite equal-arm persistence

Let A and B be finite products of functions (3) evaluated at integer
multiples of z, allowing equal-arm factors too. Suppose a positive even
integer L is divisible by all their source denominators and the normalized
integer identity is

    A(m)=B(m) product_i U(Lm/2;t_i,h_i),  m=0,1,...,      (7)

where sum_i t_i and sum_i h_i^2 are finite and t_i>0. Then the countable
family indexed by i is finite.

Indeed A and B are bounded on the right half-plane and meromorphic globally.
The inherited Carlson bridge makes the product in (7) holomorphic of zero
exponential type there. Carlson applied to their difference extends (7) to
that half-plane. The inherited off-pole small-cell bound extends the product
normally off {-1/L,-3/L,...}; remove the discrete multiplier pole sets too
and apply the identity theorem on the resulting connected domain.

If infinitely many cells persist, the inherited theta/Rouche argument gives
infinitely many distinct zeros of the product tending to one same point
p in {-1/L,-3/L}, but unequal to p. In a sufficiently small punctured disk
about p, B has no poles. Thus these are zeros of A. A is meromorphic at p,
and multiplying by a fixed power of z-p makes it holomorphic there. It
cannot have those accumulating zeros because A(0)=1. Contradiction.

This uses the full proof of the earlier
[finite-persistence theorem](../continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md),
including summable small-cell convergence and off-pole zeros; it does not
assert meromorphicity of the infinite product at p. The finite factors need
not be identified or cancelled one by one.

## 6. Exact relevance and remaining obligation

The companion [normalization lemma](UNEQUAL-RESOURCE-NORMALIZATION.md) explains
when a raw diagonal identity supplies (7) and the squared-bias budget. This
separates the analytic claim from an unproved observation decoder.

The original class allows irrational alpha=b/(a+b). No integer subsequence
then centers alpha n at an integer. Its moving fractional part remains in
the Gaussian sum. The inherited finite COMMON divisor palette fixes arm
differences and routing coins, but not this ratio of the two absolute arm
durations. Thus neither target finiteness nor COMMON support proves the
arithmetic premise for the finite factors arising on both sides of a limit.

The result discharges the continuation/finite-persistence step in precisely
the stated rational-factor setting, without a bound on the number of equal
cells. It does not establish general private finite forcing, a general
original-source observer, INDEPENDENT local exclusion or G4 impossibility.

Classical inputs are the integer Gamma shift formula, Stirling asymptotics,
Carlson uniqueness and the previously proved source application of Rouche.
Primary formula references: [DLMF 5.5.1](https://dlmf.nist.gov/5.5.E1) and
[DLMF 5.11.3](https://dlmf.nist.gov/5.11.E3); the earlier Carlson proof records
its original research reference. This note makes no historical priority
claim for the Gamma-ratio construction. Its exact source applicability and
arithmetic limitation are the research claims being checked.
