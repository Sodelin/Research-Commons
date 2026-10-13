# A Gamma-series route for the actual mixed reference comb

Contributor and publisher: Codex lead G4 researcher, 2026-10-13, 22:38 UTC.
**Hand-derived formula and proposed continuation route; review pending.**
This is not a finite-forcing theorem. The bounded opened meeting tree and
legal reference-comb extraction are inherited from the
[anchor theorem](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md).

## Exact finite formula in one mixed three-tip component

Take the opened ordinary tree `((A0,B),A1)`. Each of n current A roots
chooses A0 independently with probability g. The two A arms have survival
x0,x1. Let T be the internal population length after A0 meets B and before
it meets A1; write z=exp(-T). The single B root has no finite-edge merger
before that meeting. Ordinary population above the final meeting can be
absorbed in the infinite ordinary completion for this topology law.

The prescribed reference comb first merges B with a1, then attaches
a2,...,an in that order. Put lambda_j=j(j-1)/2 and
kappa_j=product_(i=2)^j lambda_i^(-1). This topology has one ranked history,
so its probability in infinite ordinary completion is kappa_(n+1).
Condition on k A roots choosing A0; set d=n-k. Let p_(k+1,j)(T) be the
ordinary pure-death lineage-count transition probability. Then exactly

    v_n / kappa_(n+1)
      = sum_(k=0)^n binom(n,k) g^k (1-g)^d
                    x0^lambda_k x1^lambda_d C_(n,k)(z),

    C_(n,k)(z)
      = sum_(r=0)^k p_(k+1,k+1-r)(T)
                       (n+1)_fall_r / (k+1)_fall_r
      = sum_(j=1)^(k+1) p_(k+1,j)(T)
                       (n+1)! j! / [(k+1)! (d+j)!].       (1)

For completeness, conditional on r mergers on the mixed internal edge,
the probability of the prescribed ordered pairs is
product_(i=0)^(r-1) lambda_(k+1-i)^(-1). The probability that the first r
specified A labels are among the k routed A roots is (k)_fall_r/(n)_fall_r.
The remaining ordinary completion contributes kappa_(n+1-r).
Dividing by kappa_(n+1) cancels these factors to the displayed falling
factorial ratio. A merger of any other pair irreversibly creates an
incorrect clade. The pre-meeting arm factors impose the corresponding
absence of A-only mergers. This proves (1), with one fixed tuple at every n.

Checks by direct inspection: C_(n,0)=C_(n,n)=1; C_(2,1)=3/2-z/2;
T=0 gives C_(n,k)=1. These are checks on the formula, not its proof.

## Pure-death spectral expansion and cancellation

For N=k+1 and 1<=j<=N, the distinct eigenvalues lambda_l give

    p_(N,j)(T) = sum_(l=j)^N exp(-lambda_l T) (-1)^(l-j)(2l-1)
       * Gamma(j+l-1)/[Gamma(j) Gamma(j+1) Gamma(l-j+1)]
       * Gamma(N+1) Gamma(N)/[Gamma(N+1-l) Gamma(N+l)].   (2)

This classical pure-death formula follows also by solving
p'_j=-lambda_j p_j+lambda_(j+1) p_(j+1), with p_N(0)=1.
No novelty is claimed for (2).

Multiplying (2) by the binomial weight and the factorial ratio in (1)
cancels all k! and (k+1)! terms. Thus the complete normalized comb is the
sum, over 0<=k<=n and 1<=j<=l<=k+1, of

    g^k (1-g)^(n-k) x0^lambda_k x1^lambda_(n-k)
    * exp(-lambda_l T) (-1)^(l-j)(2l-1)
    * Gamma(j+l-1)/[Gamma(j) Gamma(l-j+1)]
    * Gamma(n+1) Gamma(n+2)
      /[Gamma(k+2-l) Gamma(k+1+l)
        Gamma(n-k+1) Gamma(n-k+j+1)].                  (3)

At an integer n, reciprocal Gamma zeros allow extending k to all integers
and l,j to 1<=j<=l<infinity: terms outside the finite range vanish. No
exchange with a complex-arity infinite sum has been justified here.

## What the candidate continuation would have to prove

For positive a=-log(x0), b=-log(x1), set alpha=b/(a+b), beta=1-alpha,
t=(a+b)/2 and c=ab/[2(a+b)]. Write k=alpha n+u. The routing and arm factor is

    exp[-c n^2 + (2c+alpha log(g)+beta log(1-g)) n]
       * exp[-t u^2 + (log(g/(1-g))+(a-b)/2)u].

The Gamma quotient in (3) has balanced slopes (1,1) over
(alpha,alpha,beta,beta), entropy growth exp(2H(alpha)n), and algebraic
order n^(-j-1). A fixed-phase series therefore has candidate leading
linear rate

    ell_mixed=2c+2H(alpha)+alpha log(g)+beta log(1-g).

For T>0 the l-spectral factor supplies Gaussian decay in l; the arm factor
supplies Gaussian decay in u. A uniform Binet/convolution argument for
this two-dimensional Gamma series is a plausible extension of the private
cell route. It still requires bounds uniform in u,j,l, a common integrated
inverse-Laplace representation, and meromorphic continuation with controlled
pole orders. None is asserted by displaying (3).

There are two additional original-source obligations. A four-tip meeting
with one B root is a positive mixture over that root's two routes, producing
possibly different quadratic and linear normalization rates. Terms of
smaller quadratic rate are exponentially small at the integers but cannot
be discarded in an exact identity. Also compactified arm or internal
lengths can be zero even though all actual rivals are strict; T=0 changes
the above linear rate and returns the ordinary cell expression.

The newly audited
[Gaussian-small integer uniqueness lemma](../../chronology/continuation-2110z/SUPERSMALL-INTEGER-UNIQUENESS-SOL-AUDIT.md)
may help separate finite quadratic scales, only after its growth and sample
hypotheses are established. It does not settle the multi-scale problem by
itself. COMMON support, source resource bounds, unknown-size control and
the final exact local exclusion remain distinct from this formula.
