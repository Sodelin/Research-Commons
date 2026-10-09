# Independent local-certificate audit

Reviewer: Codex independent validation lane. Scope: source inspection, hand
inequalities and independent exact replay; no kernel proof of the source provider.
Reviewed production SHA256:
`400f96e37b9809afd0dc349f3f08a1f9e4284dead247d68580060592553d29a2`.

The rational separator uses q=1/2, p=3/16 and COMMON clock c=2/5, with
arities 2..4. Exact tangent annihilation and positive Bernstein coefficients
certify the complete interval 1<=y<=1/c. No mesh supplies the sign. Independent
replay returns lower bound 297812501/297812500, epsilon approximately 2.84e-5
and eta approximately 1.04e-11 in the maximum norm of (p,y=1/q).

The reported neighbourhood constants are conservative. With w=p(y-1), the
actual polynomial identity is R=1+wD+w²E. For 0<w<=epsilon<=1 and R>=1,
|log R-wD|<=w²[Emax+(Dmax+Emax)²/2]. Consequently the chosen epsilon makes
each extra cell's separator value at least d w/2, uniformly over rare coins.

The Hessian bound uses R>=1 and
|partial_ij log R|<=|partial_ij R|+|partial_i R| |partial_j R|.
Summing absolute coefficient bounds and applying Taylor's theorem in two
coordinates gives the reported factor 2 Hmax times the squared maximum norm.
Tangent annihilation eliminates the linear body correction.

Let S be the sum of all extra-cell w values. Exact first-two diagonal equality,
log(1+x)<=x and 1-exp(-x)<=x imply
|w-w0|<=R2max S and |R3-R3target|<=3 R3max (1/c+1) S.
Substitution in y=(R3-1)/(3w)-1 and p=w/(y-1) gives the code's cy and cp
bounds, using positive rectangle denominators. Thus body displacement is at
most max(cp,cy) S. Independently, log(1+2w)>=2w/(1+2epsilon) implies
S<=(1+2epsilon)[(ymax-1)+pmax] eta. The chosen eta therefore makes the
quadratic body error smaller than the positive extra-cell linear score whenever
S>0. This derivation has no constant depending on the number of extra cells.

The provider still requires an actual equal-arm word, one persistent biased
body already inside that neighbourhood, the same observed positive COMMON
clock and exact normalized diagonals through the certified arity. The software
checks one supplied finite word, and explicitly leaves all-rival localization
false. It does not establish arbitrary-source admission from stochasticity,
target-neighbourhood coverage, general algebraic RCF search, whole-tree legal
observation decoding or general G4 stopping.

The source-audit correction separating neighbourhood membership from **all**
theorem premises was accepted: exact diagonal matching is now included only in
`local_theorem_full_premises_verified`. This is a flag/provenance correction,
not a new mathematical theorem. Prior source providers retain dot attribution.
The arity-12 cone weights remain conic coefficients, not physical source-word
multiplicities or a source mixture operation.
