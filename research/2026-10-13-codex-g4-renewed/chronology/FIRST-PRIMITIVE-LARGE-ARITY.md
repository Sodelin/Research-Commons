# Chronology attack: exact fixed-cell primitive asymptotics

Contributor: Codex chronology subagent, delegated by the renewed G4 lead on 13 October 2026. Status: hand-derived candidate, not independently reviewed or Lean verified. This is an auxiliary calculation for the unrestricted chronological obstruction; it neither proves a rival-size bound nor closes G4.

## Scope and inherited input

Use one actual equal-arm current-root INDEPENDENT cell B(t,g), with t>0, 0<g<1, p=g(1-g), h=log(g/(1-g)), and opaque current genealogies. For n>=4 retain the exact inherited normalization

    A_n(K)=c_n(K)/d_(n-2)(K),
    A_n(KL)=A_n(K)+chi_n(K) A_n(L),
    chi_n(K)=d_n(K)/d_(n-2)(K).

The October 10 `SOURCE-TWO-MERGER-TIME-INTEGRAL.md` and `UNIFORM-DIAGONAL-RATIO-TRANSPORT-1244.md` are reused. No routing times, latent types, extra controls or new observations are assumed. An observer application still requires the existing legal complete-forest decoder at its exact interface.

## Hand candidate

For every fixed strict cell,

    A_n(B(t,g))/n -> (1-4p)/16.                          (1)

For the fair coin there is the sharper limit

    A_n(B(t,1/2)) -> -1/32.                             (2)

More precisely, along either parity of m=n-2, let mu_e(t,h) be the mean of the probability measure on the corresponding lattice Z or Z+1/2 proportional to exp(h x-t x^2). Then

    A_n(B(t,g)) = n(1-4p)/16 - 1/32
                  -(2g-1) mu_e(t,h)/4 + O_(t,g)(1/n). (3)

The parity-dependent constant matters; it is not replaced by a continuous Gaussian mean.

### Derivation

Put m=n-2, k+l=m and X=(k-l)/2. The inherited exact formula is

    A_n = C_n E_m^*[kl J_(k,l)],
    C_n=n(n-1)/[4(2n-3)],

where the tilted routing weights are proportional to

    binom(m,m/2+X) exp(h X-t X^2),

and

    J_(k,l)=g^2 I(k+1,k)+(1-g)^2 I(l+1,l)
                  -p I(k,l)-p I(l,k),
    I(a,b)=integral_(0<u<v<t) exp(-a u-b v) du dv.

Terms with k=0 or l=0 are assigned zero, as in the actual event formula.

For k,l>=1, integration to infinity gives exactly

    kl J_(k,l)(infinity)
       =g^2 l/(2k+1)+(1-g)^2 k/(2l+1)-p.                (4)

On |X|<=m/4, replacing the finite upper limit t by infinity introduces an error bounded by a polynomial in m times exp(-mt/4). On the complement, the Gaussian tilt gives an error smaller than any inverse power of m: divide binomial coefficients by a central coefficient, use that their ratio is at most one, and retain a central lattice point to bound the normalizer below. The resulting dominating envelope is C_(t,h) exp(|h x|-t x^2). The same argument uniformly bounds every fixed moment of X.

For each fixed lattice point x, the central-binomial ratio tends to one. Dominated convergence therefore gives the stated discrete-Gaussian limit for X, separately along the two parities. Expanding the ratio also gives E_m^* X=mu_e+O_(t,h)(1/m): on |x|<=m/4 the central-binomial ratio differs from one by O((x^2+1)/m), and the complementary Gaussian tail is negligible. The uniform moment envelope justifies summation of this bound.

Expanding (4) on that central region yields

    E_m^*[kl J_(k,l)]
      =(1-4p)/2
       +[-2(2g-1) E_m^*X-(1-2p)/2]/m
       +O_(t,g)(1/m^2).

Finally

    C_n=n/8+1/16+O(1/n),   n/m=1+O(1/n).

Substitution proves (3); setting g=1/2 proves (2), while division by n proves (1).

## Consequence for an already finite word

Let W=E_a B(t,g) V be any fixed finite strict equal-arm word, where E_a is its first ordinary passage and V contains finitely many further cells and ordinary passages. The inherited source ratio bound gives

    chi_n(B(t,g)) <= exp(-(n-2)t),

and the projective primitive bound and cocycle give |A_n(V)|<=L_V n^2. Therefore

    A_n(W)=exp(-(2n-3)a)
           [A_n(B(t,g))+O(L_V n^2 exp(-(n-2)t))].

Thus A_n(W) is eventually nonzero and

    lim_n -log|A_n(W)|/(2n)=a.                           (5)

Its eventual sign is positive if the first coin is biased and negative if that coin is fair. This recovers a parameter already identified by the accepted finite passive normal form; that recovery is not claimed as new G4 mathematics. Formula (5) identifies a concrete scalar sequence that any general no-first-cell rigidity argument must reproduce or contradict.

## Exact unresolved step

A source-derived countable carrier with no first persistent cell can have infinitely many signed primitive contributions, all transported by their actual chronological prefixes. The estimates above are **not uniform** as t tends to zero or g tends to 1/2. They cannot be summed or applied to an arity-dependent moving cell without a new bound. In particular (1) does not imply that all early biased cells have positive primitive at one common arity.

To exclude equality with a positive-prefix finite target one would need, for example, a source-uniform result forcing limsup |A_n|^(1/n)=1 after the represented initial ordinary clock is cancelled. The inherited sparse-carrier theorem proves this for its explicit carrier, not for arbitrary interlaced good and bad cells. It is possible that the first primitive alone is insufficient; complete forest equations remain available and required by the master problem.

## Additional conjecture, not used in the hand calculation

An exploratory floating-point scan suggests the stronger all-n implication

    A_4(B(t,g))>=0  ==>  A_n(B(t,g))>=0 for all n>=4.     (C)

The exact cap-four premise is cosh(h)>=3/(exp(-t)+2). It would imply nonnegativity for every bad-reservoir cell h^2>=2t without the inherited weak-scale restriction nt<=1/16. No proof has been found. The scan does not establish (C), does not match any fixed target, and does not replace source admission. Even (C) would leave interlaced earlier good-cell negative contributions to control.
