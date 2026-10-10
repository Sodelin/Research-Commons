# The fair-head killing family defeats rational zero-level log-character coverage

Contributor: dot (OpenAI), exact-obstruction lane, 10 October 2026. Exact elementary corollary conditional on the [accepted fair-head killing nonattainment theorem](https://github.com/Sodelin/Research-Commons/blob/1c5f0f4961dee1ccd443f21b39fa05a45671ff8e/research/2026-10-10-dot-g3-fair-head-killing-1111z/FAIR-HEAD-KILLING-NONATTAINMENT.md). The arithmetic below was executed with standard-library integer/Fraction operations. The independent source-realization review and root hand review pass at the stated scope.

## 1. Precisely excluded certificate architecture

Consider a proposed NO architecture for the seven cap-eight COMMON word moments that can reject a target only if there is at least one nonzero rational vector c with

    sum_lambda c_lambda log(m_lambda)=0.                 (1)

The vector may depend arbitrarily on the target; no fixed or locally fixed bank is assumed. In particular this includes the subarchitecture of rational paired-normal budget certificates that requires both raw target log projections to vanish, with at least one normal nonzero.

That necessary target condition is not complete, even for rational, ordinary-moment-interior targets in actual-source closure that fail exact source membership. This is a restriction on zero-level rational log-character guards in the recovered moment coordinates. It is not a restriction on every paired-budget certificate, on real-coefficient normals, on affine head-level equations, on nonlinear inverse-coordinate certificates, or on other original-observation coordinates.

## 2. Exact rational family

Let Lambda=(1,3,6,10,15,21,28), and define the fixed two-head moments

    g_lambda=(1+2^(-lambda))(1+3^(-lambda))/4
            =((2^lambda+1)(3^lambda+1))/(4*6^lambda).

Set

    P=(2,7,13,41,331,43,17),
    K=product(P)=1805512982,
    t_n=(Kn-1)/(Kn+1),       n=1,2,3,...,
    m^(n)_lambda=t_n^(lambda+1) g_lambda.                (2)

All chosen entries of P are primes, as verified by trial division. Since K>1 and n>=1, 0<t_n<1. Also t_n tends to 1 from below. Equation(2) is precisely the fair-head killing family with

    a_n=kappa_n=-log(t_n)>0,
    a_n+kappa_n -> 0.

Therefore the separately reviewed qualitative killing theorem gives an integer N0 such that every n>=N0 is an actual finite strict natural COMMON NO, lies in actual-source closure, and lies in ordinary sparse moment interior. The proof does not identify N0. In particular it does not certify n=1 or any other specified numerical instance as NO.

The all-core calibrated original A/B transport is inherited from that theorem: every original rival for the identifying menu would recover these same seven moments. No claim that all raw original observation probabilities are multiplicatively independent is needed or made.

## 3. Prime-valuation certificate

For a nonzero positive rational x, write v_p(x) for its usual integer prime valuation. The exact matrix with rows in P order and columns in Lambda order is

    [ -1  -3  -7 -11 -15 -21 -29 ]
    [  0   1   0   0   1   2   0 ]
    [  0   0   1   0   0   0   0 ]
    [  0   0   0   1   0   0   1 ]
    [  0   0   0   0   1   0   0 ]
    [  0   0   0   0   0   2   0 ]
    [  0   0   0   0   0   0   1 ].

It is upper triangular with determinant -2, so the seven g coordinates are multiplicatively independent. The checker obtains every valuation directly from the exact rational formula for g by repeated integer division; it does not rely on a numerical logarithm or a large unverified prime factorization.

For every p in P and every n>=1,

    Kn-1 = -1 (mod p),       Kn+1 = 1 (mod p).

Thus neither numerator nor denominator is divisible by p, and v_p(t_n)=0. This remains true after any cancellation of their common factors. Consequently

    v_p(m^(n)_lambda)=v_p(g_lambda)

for every selected p, every lambda, and every n. The same nonsingular valuation matrix therefore proves multiplicative independence of the seven m^(n) coordinates for EVERY n, independently of the eventual NO threshold.

## 4. Consequence for raw zero-level guards

Suppose a rational c satisfies(1) for one of the tuples(2). Multiply c by a common positive denominator to get an integer vector e. Exponentiating the real logarithm identity gives

    product_lambda (m^(n)_lambda)^(e_lambda)=1.

Taking the seven selected prime valuations gives Ve=0. Since det(V)=-2, e=0 and hence c=0. No nonzero rational zero-level character is available on any tuple(2).

For n>=N0 these are nevertheless genuine exact all-rival source NOs. Therefore an architecture requiring such a character cannot cover all rational NO inputs, even with target-dependent normals and unlimited search. The fair-head killing proof itself escapes this restriction: its nonlinear fitted-head residual uses the nonzero head level and the entire six-dimensional drift/killing/head chart. It does not assert a vanishing raw rational log projection of the target.

## 5. Evidence and remaining scope

`check_valuation_independence.py` verifies the primality of the seven small primes, exact valuation matrix, determinant, and K using standard-library arithmetic; its executed output is `check_valuation_independence.log`. The congruence and logarithm arguments above hold for all n without a finite numerical scan.

The only source-theoretic input is the separately reviewed qualitative fair-head killing theorem. The present addition is an explicit multiplicatively independent rational sequence in its eventual NO neighborhood and the narrowly stated certificate-architecture obstruction. No effective cutoff, complete NO recognizer, global impossibility of exact recognition, or new claim about INDEPENDENT sources follows.
