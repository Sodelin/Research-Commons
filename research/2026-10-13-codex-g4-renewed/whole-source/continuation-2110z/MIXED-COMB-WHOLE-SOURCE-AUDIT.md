# Independent hand audit of the strict mixed-comb continuation

Reviewer: Codex whole-source lane, 13 October 2026.
**Verdict: accepted at its stated strict single-component scope.**
This lane authored the earlier anchor invariant and three-tip gauge notes,
but did not derive the two manuscripts audited here. This is a mathematical
hand audit, not a new numerical test, formal proof or general G4 conclusion.

Pinned manuscripts:

* [Fixed-phase Laplace proof](MIXED-COMB-FIXED-PHASE-LAPLACE.md), SHA256
  `1dc494de0e83c7c209280a5787709bd6dec4daf5d0593fc8b8afb4cd8ae6540d`.
* [Root's physical formula](MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md), SHA256
  `e26a0ef00f2cd75a3e0a7ae77394d43a1b6e1f8d7cc8c3a782d69880169efa15`.

## Source formula and normalization

I independently rederived the formula using the actual selected-lineage
process on ((A0,B),A1). Conditional on k of n labelled A roots choosing
A0, their subset is uniform. Conditioning further on r internal-edge
mergers, the prescribed comb requires the first r specified A labels in
that subset, with probability (k)_r/(n)_r. Its successive pair choices
have probability product_i lambda_(k+1-i)^(-1); all other pair choices
create an irreversible forbidden clade. The remaining ordinary completion
has probability kappa_(n+1-r). Their ratio to kappa_(n+1) is exactly
(n+1)_r/(k+1)_r. The two lower A-arm no-merger factors are necessary and
do not bias the label subset once k is fixed. This verifies equation (1).

The pure-death coefficients in equation (2) follow by substituting
lambda_r-lambda_l=(r-l)(r+l-1)/2 into the distinct-rate partial fractions.
Multiplication by binom(n,k) and the comb factorial ratio cancels the
stated factorials, giving exactly equation (3), including j's denominator.
At integer n, k<0 or l>k+1 is killed by 1/Gamma(k+2-l), while k>n is killed
by 1/Gamma(n-k+1). Thus the infinite-series notation reproduces the finite
physical expression; it is not a new observational mixture.

Square completion gives the claimed c, h and ell. The extra entropy
H(alpha) compared with a private-cell diagonal comes from the comb
completion factor, so the total 2H(alpha) is correct. The cases k=0,
k=n and n=2,k=1 also agree directly with the process.

## Uniform Gamma estimates and poles

The four shifts relative to the squared base quotient are

    s+1-l, s+l, -s, j-s,

and their sum is j+1. For a nonnegative integer shift, each denominator
factor gamma*z+delta+q is bounded below by a fixed positive multiple of
1+|z|+q on Re z>=0, since delta>=1/2. A negative shift is a polynomial
product, bounded above by [C(1+|r|)(1+|z|)]^|r|. Hence the recurrence
bound is uniform even when shifts grow with z. The base quotient is
O((1+|z|)^(-1)), while Gamma(z+2)/Gamma(z+1)=z+1. These two factors
cancel in order, leaving the claimed (1+|z|)^(-j-1).

The resulting exp(CN log(2+N)) coefficient is summable against the two
strict Gaussians in s and l, including the spectral coefficient and the
j sum. This verifies the uniform O((1+|z|)^(-2)) right-half-plane bound.
It requires a,b,T>0; the constants are not asserted uniform at T=0.

For an arbitrary compact z set, shift the base Gamma arguments by one
fixed sufficiently large positive integer before applying the same
recurrence. The shifted base arguments have positive real parts; their
reciprocals are uniformly bounded on the compact set. After removing the
common numerator Gamma(z+1)Gamma(z+2), normal convergence therefore gives
an entire sum. No spurious recurrence poles remain. The only possible
poles of F_mix are negative integers, of order at most two; at -1 the
common numerator has only a simple pole. Complex phase in a sufficiently
small strip preserves these estimates, and reindexing s gives periodicity.

## Laplace density and all orders

The logarithmic kernel's 1/v terms cancel by alpha+beta=1. Its constant
is j+1: the two numerator shifts contribute -2, while the four denominator
shifts contribute -(j+3). Thus [S(v)-(j+1)]/v is analytic at zero.
Differentiating the logarithmic Gamma quotient twice yields exactly the
Laplace integral of v^2K(v), and real-axis Stirling asymptotics remove
both affine integration constants. The stated leading coefficient
nu=(2 pi)^(-1) alpha^(-2u-2) beta^(2u-j-1) also checks directly.

Multiplying the numerator of K by v leaves an analytic function with a
double zero. Its second derivative has the claimed O(N^2) exponential
shift bound on the common disk/sector. The convolution simplex formula
then gives Gamma(r+j+1) in the denominator of the r-th term. Together
with r! this yields the Bessel-type exponential bound in sqrt(N^2|v|),
so h/v has the stated exp(C_R N) compact bound. Both Gaussian sums can
therefore be taken on the common analytic domain.

For each fixed index triple, K and its convolution exponential have
exponential order on the positive axis. The initial Bromwich inverse is
valid because W decays at least quadratically on vertical lines. Shifting
its contour to a common Re z=c0>0 crosses no poles; the horizontal sides
vanish by the already uniform right-half-plane estimate. Summing only
after this shift supplies the subexponential density bound. This avoids
the invalid inference of a global Laplace transform from a bound of the
form exp(Cv^2).

Only j=1 contributes to the leading density coefficient. Its l sum is
Xi(T). The finite-death multiplier is product_(r=1)^(l-1)(M-r)/(M+r),
which lies in [0,1] and tends to one. Gaussian domination gives Xi as
lim_M p_(M,1)(T). The expected time from M to L is at most 2/L, so the
stated Markov/strong-Markov argument gives a uniform positive lower bound
on that limit. Thus the leading coefficient is uniformly positive on
the phase circle. The common Taylor radius and density tail bound justify
the uniform Watson expansion to every fixed order.

Finally, finite products have convolution densities of the stated power
times an analytic germ. For equal total power, all-order flatness kills
that germ, then its continuation along the positive axis, then its
Laplace transform. The extension combining integrated private and direct
mixed inverses has the indicated powers 3/2 and 2. This analytic exactness
does not itself provide a scalar source identity or separate distinct
quadratic/linear mixture rates.

## What still survives if the strict scalar class closes

Even if the separate finite-mixture argument closes every STRICT mixed
reference scalar, the original-source transfer still needs the following.

1. **Actual shared-source compactification.** Apply the finite COMMON/G1
   core reduction, preserve one tuple and all residual slots, and control
   its bounded-core limit. A strict sequence can reach zero arms, zero
   mixed internal length or endpoint core coins. The present proof does
   not cover those boundary components merely by continuity; its leading
   rate and analytic class change there.
2. **Removal of unequal COMMON/INDEPENDENT weak clocks.** Finite persistence
   alone leaves a finite limiting body with effective INDEPENDENT gaps
   A^I and larger COMMON expenditures A^C. In the private proof, full
   finite chronology identifies that body with T, so the minimum COMMON
   budget forces every A^C-A^I to vanish. An arbitrary original finite
   body with T's INDEPENDENT law has not been identified that way. One
   needs a source theorem excluding a nonzero weak clock deficit even
   when the finite core changes, or another direct law-forcing argument.
3. **Original-source local exclusion.** After that clock issue is resolved,
   a theorem must exclude arbitrary numbers of weak private extras while
   the shared finite core parameters also vary, around every relevant
   target-equivalent limiting body. The general private local theorem
   assumes a nearby identifiable private body and a fixed COMMON minimum;
   neither the anchor ratio nor same-exterior tomography supplies those
   premises for a changing original core.

These are precise missing implications, not evidence of a negative G4
answer. This audit provides no fixed-target exact inequivalent rival after
every finite prefix, no illicit latent queries, and no rival-size bound.
