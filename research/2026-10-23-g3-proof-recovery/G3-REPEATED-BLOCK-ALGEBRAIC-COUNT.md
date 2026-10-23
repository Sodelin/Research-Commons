> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# A terminating repetition bound from algebraic multiplicative rank

22 October2026 UTC, existing G3 owner. HAND/self-audited, UNREVIEWED and
UNCOMPILED. This is a count bound for repetitions of ONE supplied block
family, with a supplied exact algebraic diagonal target. It is not the full
G3 witness bound. No RCF, PARI, compiler, source/model/native job or new
mathematical program was run; the example below is hand arithmetic.

The distinction from unrestricted words is essential: the block's numerical
parameters are the SAME in every repetition. Fresh physical sites and bits
are distinct. This is a search family, not an extra constraint imposed on
the original G3 problem or on every possible rival source.

## Exact claim and reused suppliers

Supply a semialgebraic parameter domain Omega over real algebraic constants
and a rational map

    f:Omega subset R^d -> R_(>0)^s,

with denominators nonzero on Omega. Supply positive effectively algebraic
b=(b_1,...,b_s). Let r be their multiplicative rank: the rank of the subgroup
they generate. Assume r>d. Then there is a TOTAL computable integer H(f,b)
such that, for every positive integer N and every theta in Omega,

    f_i(theta)^N=b_i for all i  =>  N<=H(f,b).                 (1)

H is computed without assuming that any solution exists, including on NO
inputs. Once it is computed, exact fixed-N polynomial feasibility for
N=1,...,H decides this repeated-block family. A full fixed-N source compiler
may impose additional joint equations; the same necessary bound still
applies. H=0 means there is no positive repetition count.

The closest retained count statements, variable-N construction and later
parametric review were inspected before this argument at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:

- research/2026-10-10-dot-g3-real-critical-finiteness-1446z/
  ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md bounds the retained count in
  its specified paired-critical positive-residue predicate. It expressly
  does not bound arbitrary actual words. No criticality or Poisson residue
  is assumed in (1). Its accepted/current SHA256 is
  52b4b1cba30ebd792b3c8b47c81e071d232c18491c67be634decd79018fa4688;
  the complete later INDEPENDENT-ALL-REAL-CRITICAL-FINITENESS-REVIEW.md,
  SHA25689edb2ef58d6c37758e22b57c6536fec5eab1fbd9873bb98cae0b61dfb98119a,
  was also read. Its scoped acceptance does not acquire the count in (1).
- research/2026-10-10-dot-g3-variable-count-exact-slice-1300z/
  VARIABLE-COUNT-EXACT-SLICE.md and the later parametric-certificate review
  supply a different, already solved variable-count construction: an N-cell
  primary group plus a retained head and secondary correction. Those other
  factors cannot be divided out as known target coordinates. Their forcing,
  rank and tail-certificate hypotheses remain; none is supplied here anew.
- The old source/path REDUCTION.md at9d21c0727564ae0ba101039d97b07c614d17f2e1,
  research/2026-10-06-dot-g3-global-source-reachability-0019z, already supplies
  fixed-shape RCF feasibility and actual-source reconstruction. These are
  REUSED, not a new solver or graph constructor.
- The retained integer-power/root-descent audit remains in force. Here a
  positive root is a NECESSARY algebraic signature of a supposed repeated
  witness. It is not declared a physical operation; actual feasibility is
  checked separately at each of the finitely many N.

The arithmetic supplier is the main theorem on printedp626 of
[Mordell1953](https://msp.org/pjm/1953/3-3/pjm-v3-n3-p10-s.pdf).
For a real number field K and real radicals x_j with x_j^N in K, it gives
K-linear independence of the monomials with exponents0,...,N-1, provided
no monomial in the x_j lies in K unless each exponent is divisible by N.
The publisher text's statement, lemma and proof were read. Its prime-radical
special case is the older Besicovitch theorem, restated on printedp625.
These are REUSED arithmetic, not new independence theorems or novelty claims.

The incremental interface is (1) for a supplied rational signature family.
A bounded Markdown prior search is navigation, not a worldwide absence claim.

## Effective saturated coordinates, without a logarithmic zero oracle

Take a real number field K containing b and every coefficient of the supplied
family. Let S consist of the prime ideals supporting the principal fractional
ideals (b_i). Compute a basis epsilon_1,...,epsilon_t of its POSITIVE S-units,
positive at the selected real embedding. This group is free: a field embedded
in R has only the roots of unity+/-1, and its positive torsion is trivial.

This is standard effective algebraic number theory, not a transcendence
premise. For clarity, an unconditional acquisition argument is as follows.
Dirichlet's known unit rank lets one enumerate integral units and rational
enclosures of their logarithmic embeddings until a full-rank tuple is
certified. Only a NONZERO determinant has to be found; zero determinants
need not be decided. Its log parallelepiped bounds representatives modulo
the generated finite-index subgroup. A computable rational bound on all
Archimedean absolute values bounds their coordinates in an integral basis.
Enumerating that finite integer box supplies the remaining ordinary units.

For each prime ideal P in S, dovetail powers P^h and algebraic integers until
a generator is found; finiteness of the ideal class group guarantees success.
Their valuation vectors give independent multiples of every S-coordinate.
Reduce S-valuations to finite residue ranges using those generators, then
reduce Archimedean logs using the ordinary-unit tuple. The norm is bounded
on those valuation ranges. By the product formula the remaining log coordinate
transverse to the ordinary-unit hyperplane is bounded too. Thus another finite
integral-basis box contains
representatives for the remaining positive S-unit quotient. This obtains a
finite generating set. Its rank is the ordinary-unit rank plus |S|.

Enumerate exact algebraic multiplicative relations between these generators
until the required number of independent relations is found. Saturating that
relation lattice gives the entire kernel, since the positive group is
torsion-free. Smith normal form then extracts a basis. All equality tests
here are algebraic product tests; no nonlinear logarithmic equality is used.

As a practical implementation caution, the official PARI documentation marks
uncertified bnf data as GRH-dependent and requires full certification before
unconditional uses, including S-units. An attempted online full-page read
failed; its indexed official contract was inspected, not a complete current
manual or an execution. No PARI call or installation is selected here. The
termination argument above does not assume a provisional class-group result
or termination of a certification call on incorrect data.

Write the b_i as products of the epsilon_j, obtaining an integer t-by-s
matrix W. Those coordinates can be found by exact product enumeration since
membership is already known. Let U be an integer basis for

    span_Q(columns W) intersect Z^t.

This lattice is primitive. Compute D with W=U D. It has r rows and full row
rank. Define C_j=product_l epsilon_l^(U_lj). Thus

    b_i=product_j C_j^(D_ji).                                (2)

If g=product_j C_j^(v_j/N) lies in K, it is a positive S-unit: its Nth power
is an S-unit, so every valuation outside S is zero. Write its integer
S-unit coordinates as z. Then N z=U v. Primitivity of U supplies an integer
left inverse, and hence every v_j is divisible by N. Mordell's precise
hypothesis is therefore acquired for x_j=C_j^(1/N), for EVERY N.

## Choose one polynomial and compute the bound

Let T be the algebraic subtorus parametrized by

    X_i=product_j Y_j^(D_ji).

Its dimension is r. The Zariski closure V of f(Omega) has dimension at most d.
Thus T is not contained in V. There exists a polynomial P over K which
vanishes on f(Omega) but whose restriction to T is nonzero.

This P is effectively obtainable: enumerate finite polynomials over K;
RCF decides their universal identity on the supplied rational map/domain,
and substitution of the displayed monomials decides whether their restriction
to T is zero. The dimension inequality proves that this search terminates.
An empty Omega can instead be rejected immediately. This is a mathematical
algorithm using the OLD fixed-formula RCF procedure, not a newly run search.

Expand P=sum_alpha c_alpha X^alpha. On T collect terms with the same
integer vector e=D alpha and discard zero summed coefficients. Let E be
the finite remaining support. It is nonempty. Define

    H=max_j [max_(e in E) e_j - min_(e in E) e_j].             (3)

For N>H, factor product_j x_j^(min_E e_j) out of
P(b_1^(1/N),...,b_s^(1/N)). The remaining NONZERO polynomial in the x_j has
degree at most H<N in each variable. Mordell's theorem makes its value
nonzero. But any solution of f(theta)^N=b has
f(theta)=b^(1/N), using positive roots, and would make that P vanish.
This contradiction proves (1). No sign test at a limiting logarithmic value,
positive distance to a boundary, or effective source-loss floor was assumed.

## A fully explicit prime-power specialization

If P has rational coefficients and b_i=p_i^(A_i/B_i), with distinct rational
primes p_i, nonzero integers A_i, positive integers B_i, and reduced fractions,
put d_i=degree_(X_i) P. Then an immediate alternative to (3) is

    H_prime=max_i floor(d_i*|A_i|/B_i).                       (4)

Indeed set z_i=p_i^(1/(B_i N)). After substituting and removing a nonzero
common Laurent monomial, exponents in z_i range over at most d_i|A_i|.
For N>H_prime this is strictly less than B_i N. Distinct monomials remain
distinct because every A_i is nonzero. Besicovitch/Mordell independence then
prevents cancellation. Negative A_i are handled by the common monomial,
not by treating a negative physical survival as allowed. The given prime/
exponent representation is exactly checkable by algebraic-number arithmetic.

## An actual repeated-bigon use-site

For k entering CURRENT roots let lambda_k=k(k-1)/2. A fresh strict natural
bigon with arm survivals x,y, parent0 probability p and ordinary survival s
has no-merger coordinates

    C_k=s^lambda_k [p*x^lambda_k+(1-p)*y^lambda_k],
    I_k=s^lambda_k sum_(j=0)^k binom(k,j)*p^j*(1-p)^(k-j)
                              *x^(j(j-1)/2)*y^((k-j)(k-j-1)/2).

Here 0<p,x,y,s<1 and original native gamma=1-p. COMMON averages one original
bit inside its cell; I routes by current root. BOTH retains the SAME p,x,y,s.
The six coordinates k=2,...,7, or the twelve paired coordinates, are rational
polynomial maps of FOUR parameters. Therefore target multiplicative rank>=5
meets r>d and gives a terminating count bound for this repetition family.

On no-merger states the block returns the same root count to its common exit,
and fresh copied sites have not been read. This is the actual constant-
continuation/freshness contract needed for product diagonals. N repetitions
give the Nth power in every displayed coordinate, even though the COMPLETE
forest kernel has off-diagonal mergers and is not replaced by that diagonal.
Same numeric p across cells does not reuse their bits; distinct original IDs
remain distinct. Opaque entering trees are not rerouted by their old leaves.

Extra ordinary prefix/inter-cell factors can be allowed for this necessary
bound: their PRODUCT survival A contributes A^lambda_k and is absorbed into
s=A^(1/N) in the diagonal equation. This asserts no reordering or equality
of the full chronological forest operators. At each bounded N the actual
source compiler must still use all the original factors and joint equations.

The high-rank case is not vacuous. At p=x=s=1/2,y=1/3 the COMMON coordinate is

    C_lambda=(3^lambda+2^lambda)/(2^(2lambda+1)*3^lambda).

For lambda=1,3,6,10,15 the numerators are respectively
5,35,793=13*61,60073=13*4621, and14381675.
The last is divisible by11; none of the previous four is. Any prime divisor
of4621 is new relative to2,3,5,7,13,61, as direct division verifies. Thus these
five coordinates are multiplicatively independent by their successive new
prime valuations. Every fixed positive repetition count gives rational
targets of rank at least5. This is hand nonvacuity arithmetic, not a new
executed source fixture, checked calendar, or claim about minimum count.

## Original-goal boundary

The target diagonals must actually be supplied, or recovered by a licensed
observation decoder such as the retained identifying COMMON calibration.
Selecting one latent diagonal from a general coupled fibre does not suffice.
The finite-N search must enforce the full declared data, source admission,
IDs, freshness, strictness, calendars and SAME physical tuple.

Failure of every N<=H rejects only this supplied repetition family. General
G3 permits unrelated parameters and heterogeneous words; it does not force
them to repeat one block. High multiplicative rank is not itself a purity
or nonpurity test. The old variable-N slice also has other unknown
head/correction factors, so its inner block is not a known root of the whole
target. Neither scope is silently replaced here. No complete original NO,
input-effective bound over all words, or goal closure follows. The acquired
result is a usable total count bound on the stated high-rank family, not
another conditional consumer with an unproved count premise.
