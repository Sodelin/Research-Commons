# Reciprocal-root order feasibility and homogeneous logarithm zero tests

Stable source key: G3-ARITH-ROOT-ORDER-LOGZERO-01.

23 October 2026. Existing G3 owner, Codex/OpenAI. Complete hand proof below:
**PROVED (not Lean formalized)**. Independent review not performed. No
scientific producer, numerical check, solver, QE, compiler or model run.
Classical Taylor bounds and Vandermonde independence are reused. Historical
priority of this equivalence has not been established.

This classifies an arithmetic receiver needed by the current root-count
route. It is not a new full G3 attack, a source-complete reduction or a
solution of the logarithm zero problem.

## 1. Prior-solution comparison before the extension

The original G3 endpoint is unchanged: total exact recognition of every
original finite algebraic joint input, with one admitted strict finite
source/ID map/physical bank on YES and exclusion of every unknown finite
size on NO. Natural positivity, original menus, CURRENT-root routing,
COMMON/I/BOTH, chronology and retained registers remain binding.

Actually compared at Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:

- Accepted predecessor
  `handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md`,
  25098B/SHA25697987236e5c6f5429d2f597ff1ebd5b34dac7078ff56515122483524a5ad968e.
  Its complete proof was read previously; the actual equality/sign boundary
  and related passages were reread for this comparison. Section4 explicitly
  says that its reciprocal-power equality theorem does not infer the sign
  of a general exponential polynomial near zero.
- Its COMPLETE later scoped review
  `research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md`,
  5446B/SHA256179b0a86bdbc37816f971cf5fe072c0258071e47a5c205ae85c0852897468af4,
  was reread. It accepts the exact equality branch while preserving the
  exceptional strict-feasibility and full-source gaps.
- COMPLETE later successor
  `handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md`,
  20193B/SHA2565c5cd7e670d670d528d0a8414ec39748e37db467e84c4d1b18f25b20056f9916,
  was already read; the exact cutoff/sign and retuned-type passages were
  reread. Finiteness there is not an effective exceptional cutoff. Its
  changing heads do not supply fixed algebraic bases.
- The completed independent-denominator ZERO/NONZERO theorem,
  [G3-ARITH-INDEP-RECIP-EQ-01](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-23-g3-independent-reciprocal-equalities/PROOF.md),
  14796B/SHA256d55eb70efa9b5e6b2f52f4c68c44caeb9724b31e7cf16cde0f3cf605414af978,
  explicitly excludes polynomial sign inequalities. It remains PROVED at
  its scope; review/Lean/implementation are separate.

All retained local authored audit/continuation archives and relevant handoff
aliases were searched before selecting this comparison. This bounded search
does not establish worldwide priority or absence from the entire corpus.

The increment below is a TWO-WAY effective reduction. Even ONE common
denominator with a SINGLE strict polynomial inequality is enough to decide
homogeneous-log signs. Conversely homogeneous-log zero tests suffice for
every finite Boolean order problem with that common denominator. There is
one proof for arbitrary input degree, rather than a degree/cap ladder.

## 2. Exact decision problems

ALG means a real-algebraic number with an effective exact representation.
All roots and logarithms in this note use their unique positive/real values.

HOM-LOG-ZERO:

    Given positive ALG b_1,...,b_k and a homogeneous polynomial
    P in ALG[X_1,...,X_k], decide P(log b_1,...,log b_k)=0.

Constant polynomials are allowed and are decided algebraically. Nonzero
values have computable signs by interval approximation once zero has been
excluded. Thus a total HOM-LOG-ZERO oracle also supplies exact signs.

ROOT-ORDER:

    Given positive ALG b_1,...,b_k, an integer nu>=1 and a finite
    Boolean formula in polynomial comparisons of b_i^(1/n), decide
    whether some integer n>=nu satisfies the formula. Return n on YES.

Every occurrence uses the SAME integer n. Coefficients are ALG and allowed
comparisons are =, !=, <, <=, >, >=. The strict-only subproblem asks for

    exists integer n>=nu: F(b_1^(1/n),...,b_k^(1/n))>0

for ONE supplied polynomial F. This is not the independent-denominator
order problem and is not a physical source-admission promise.

THEOREM. ROOT-ORDER and HOM-LOG-ZERO are effectively Turing-equivalent.
Already the strict-only ROOT-ORDER subproblem, with EVERY base in (0,1),
has this equivalence. The forward decision procedure returns a count, not
a bound on all solutions. This theorem supplies no unconditional oracle
for either decision problem.

## 3. Effective derivative bounds require no zero oracle

For finitely many fixed positive ALG alpha_j and ALG c_j put

    f(t)=sum_j c_j*alpha_j^t,  0<=t<=1.

For any given integer r>=0, one can compute a positive rational U_r with

    sup_(0<=t<=1) |f^(r)(t)| <= U_r.                 (1)

Indeed, choose rational majorants for |c_j|, |log alpha_j| and
max(1,alpha_j). Then sum their products

    sum_j C_j*L_j^r*A_j

is a rational majorant. Algebraic arithmetic and interval bounds for the
individual computable logarithms suffice. No polynomial-in-logarithms
equality is queried to obtain an U_r.

Expanding a polynomial in b_i^t into finitely many terms gives such an f:
each alpha_j is a positive algebraic product of integer powers of the b_i.
Taylor's theorem therefore gives EFFECTIVE rational remainder bounds at0.

## 4. A strict root inequality decides a homogeneous-log sign

Take an input P,b of HOM-LOG-ZERO with homogeneous degree d. Remove every
b_i=1 by substituting log b_i=0. For the remaining bases choose

    gamma_i=b_i, sigma_i=1             if b_i<1;
    gamma_i=1/b_i, sigma_i=-1          if b_i>1.

Thus0<gamma_i<1 and log b_i=sigma_i*log gamma_i. Substitute sigma_i X_i
in P to get a homogeneous polynomial Q of the same degree; its value at
log gamma is the original value. Zero/constant degeneracies can instead
be decided directly; the construction also applies to constants.

Set ell_i=log gamma_i and

    G(t)=Q(gamma_1^t-1,...,gamma_k^t-1).

Homogeneity gives

    G(t)=t^d*Q(ell)+R(t),
    |R(t)|<=M*t^(d+1),  0<=t<=1,                    (2)

for an EFFECTIVELY computed nonnegative rational M. To justify this without
knowing Q(ell), expand G as in Section3 and bound its (d+1)st derivative.
Its coefficients below degree d vanish FORMALLY, since each input factor
gamma_i^t-1 starts at order1. Its degree-d coefficient is exactly Q(ell).
Taylor's theorem proves (2). No zero test on that coefficient is used.

Introduce the additional ALG base1/2 and put

    z(t)=1-2^(-t),
    A=4^(d+1)*(M+1),
    F(t)=G(t)-A*z(t)^(d+1).                          (3)

For0<=t<=1,

    z(t)>=t/4.                                      (4)

For example z'(t)=(log2)*2^(-t)>=1/4 there, since log2>=1/2. Integrating
proves (4). These are elementary real inequalities, not numerical tests.

Equations(2)-(4) imply for every0<t<=1

    F(t) <= t^d*Q(ell)-t^(d+1).                     (5)

Consequently, if Q(ell)<=0 then F(t)<0 for EVERY such t. If Q(ell)>0,
then F(t)/t^d tends to Q(ell)>0 as t decreases to0, so F(t)>0 for all
sufficiently small positive t. In particular, for ANY supplied nu,

    Q(ell)>0 iff exists integer n>=nu: F(1/n)>0.     (6)

The right-hand side is exactly ONE strict ROOT-ORDER input:

    Q(gamma_i^(1/n)-1)-A*(1-(1/2)^(1/n))^(d+1)>0.

Every base is strictly between0 and1. All coefficients are ALG; A is
rational and computed without the desired sign/zero answer. The displayed
polynomial has degree at most d+1. Neither t^d nor an integer factor n^d
is inserted as an extra input operation; they occur only in the proof.

A total strict-only ROOT-ORDER decider applied to Q and -Q therefore
decides whether the original value is positive, negative, or zero: zero
is precisely the case where BOTH strict-existence answers are NO. Under
a separate promise P(log b)>=0, a SINGLE call decides zero versus positive.
This proves HOM-LOG-ZERO reduces to strict-only ROOT-ORDER.

## 5. Homogeneous-log zero tests decide every common-count order formula

Expand each polynomial comparison into an exponential polynomial

    f(t)=sum_(j=1)^s c_j*alpha_j^t.

Group exactly equal positive ALG alpha_j and remove zero ALG coefficients.
If no terms remain, the function is identically zero. Otherwise the alpha_j
are distinct and their real logarithms lambda_j are distinct. The square
Vandermonde matrix (lambda_j^r)_(0<=r<s,1<=j<=s) is invertible. Hence some

    f^(r)(0)=sum_j c_j*(log alpha_j)^r,  0<=r<s,       (7)

is nonzero; otherwise the nonzero coefficient vector c would be zero.

Each (7) is a homogeneous polynomial of degree r in logarithms of supplied
positive ALG numbers, with ALG coefficients. Using HOM-LOG-ZERO on these
finitely many expressions identifies the FIRST nonzero r. Its coefficient

    a=f^(r)(0)/r!

is a computable nonzero real. Interval approximation obtains its sign and
a rational eta>0 with eta<=|a|. Section3 gives rational M>=0 such that

    |f(t)-a*t^r|<=M*t^(r+1),  0<=t<=1.

Choose a positive rational delta<=min(1,eta/(2*(M+1))). For0<t<=delta the
function has the fixed nonzero sign of a. All integer n>=ceil(1/delta)
therefore have that sign. The identically-zero branch has sign zero always.

Do this for all finitely many compared polynomials and take ONE common
integer N>=nu large enough for all their sign conclusions. Evaluate the
Boolean formula using these fixed tail signs. If it is true, return n=N.
Otherwise test the FINITELY many integers nu<=n<N. At each such n, every
positive root and polynomial value is ALG, so exact ordered algebraic
arithmetic decides the formula and provides a witness when it holds.
If none holds, return NO. The tail argument excludes every omitted count.

All loops are finite. There are at most s-1 positive-degree zero queries
for a nonzero s-term function. No unbounded search for a nonzero derivative
or assumption of eventual observed sign stability is used. This proves
ROOT-ORDER reduces to HOM-LOG-ZERO and completes the equivalence.

## 6. Consequence at the actual G3 receiver

The completed reciprocal-root equality decision cannot be promoted to a
solver for ARBITRARY polynomial order constraints just by attaching exact
real-algebraic validation at each count. Even with FIXED supplied bases and ONE common count, allowing
one strict polynomial inequality has the exact homogeneous-log zero gate
above. With independent counts, that same common-count subcase remains.

For the original cone-promised homogeneous Phi(log B)>=0 stress case,
Section4 produces ONE exact strict root inequality that is feasible at
some reciprocal integer iff Phi>0; it is infeasible iff Phi=0. This is an
arithmetic reduction, not an admitted-original-source construction. It
does not show that every such polynomial is physically enforceable in G3,
nor that the constructed roots or inequality are extra legal observations.
The particular polynomial inequalities of a physical validator may have
additional structure; they require their own source-specific analysis.

The original source-complete acquisition of heads/cores, chronology, IDs,
same-bank menus and INDEPENDENT/BOTH remains separate. Moving bases in
the old successor remain outside the fixed-base theorem. A total algorithm
for actual G3 or for HOM-LOG-ZERO is NOT supplied. The next full G3 route
must discharge those exact arithmetic and source implications, or avoid
this receiver by a different complete recognition mechanism.
No undecidability conclusion follows: the equivalence proves neither
problem undecidable and establishes no transcendence conjecture.

This equivalence is complete HAND mathematics under its stated computable
input contract. Pending review, Lean and implementation do not reopen it.
No original G3 completion, historical novelty, test execution or new peer
proof/build assignment is claimed.

Immutable source links for reuse:

- [Accepted equality predecessor](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md) and its [scoped review](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md).
- [Later retuned-type successor](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md).
- [Existing homogeneous Phi and its exact source promise](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-10-dot-g3-three-log-purity-1210z/THREE-LOG-PURITY-REDUCTION.md),8368B/SHA256c99623631f972c3911f3dceba9f1b376ed2b135fd2dbc04aeae268633fcb33a9. Its actual definition Phi(u,v,z)=u^8 P(v/u,z/u), degree8 homogeneity and source-facing sign statement were reread for Section6; the complete source had already been read.
