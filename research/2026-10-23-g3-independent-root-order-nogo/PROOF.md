# Independent reciprocal-root ORDER is undecidable

Stable source key: G3-ARITH-INDEP-ROOT-ORDER-NOGO-01.

23 October 2026. Existing G3 owner, Codex/OpenAI.
**PROVED BY HAND (not Lean formalized).** Independent review has not been
performed. No numerical/symbolic control, source producer, solver, QE,
compiler, native build or model run was used.

This settles an unrestricted ARITHMETIC backend question. It is not a new
full G3 attack and does NOT prove original G3 undecidable. In particular,
no source-complete backward reduction to original biological recognition is
supplied. The original all-input terminating-NO goal remains unresolved.

## 1. Exact statement

Fix the single rational base b=1/2 and its unique positive reciprocal roots

    r_n = (1/2)^(1/n), n=1,2,...

INDEPENDENT-ROOT-ORDER asks, for an input integer polynomial Q in k variables,

    does there exist (n_1,...,n_k) in positive integers
    such that Q(r_(n_1),...,r_(n_k)) > 0?

Every occurrence of a variable uses the SAME count assigned to it. Different
variables have independently chosen counts; equal counts are permitted.

**Theorem.** INDEPENDENT-ROOT-ORDER is recursively enumerable complete.
There is no total decision algorithm, already for ONE strict polynomial
inequality with integer coefficients and this ONE fixed base.

Moreover, there exist fixed finite K and D for which the problem remains
undecidable with at most K count variables and polynomial degree at most D.
No optimized values of K or D are claimed or needed.

Thus no total input-computable bound on ONE successful count vector, defined
on NO inputs too, exists for this unrestricted arithmetic problem. Nor can
there be sound, complete, effectively checkable finite NO certificates for
all its NO instances. Each individual supplied count tuple is nevertheless
exactly checkable by ordinary real-algebraic arithmetic.

## 2. Prior comparison and attribution

The following exact predecessor/successor scopes were compared before this
derivation. They are retained results, not reopened mathematical questions.

* The accepted 03 reciprocal-power theorem at Commons
  8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
  handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/
  INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md,
  SHA256 97987236e5c6f5429d2f597ff1ebd5b34dac7078ff56515122483524a5ad968e,
  and its later scoped review
  research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md,
  SHA256 179b0a86bdbc37816f971cf5fe072c0258071e47a5c205ae85c0852897468af4.
  Its exact identity branch and effective nonzero bound do not decide signs.

* The later complete retuned-type/primitive-multiplicity successor,
  handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/
  ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md,
  SHA256 5c5cd7e670d670d528d0a8414ec39748e37db467e84c4d1b18f25b20056f9916.
  Arbitrarily large presentations there do not refute a minimum-witness
  bound; their moving physical types do not settle this arithmetic question.

* The completed independent-count ZERO/NONZERO decision
  [G3-ARITH-INDEP-RECIP-EQ-01](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-23-g3-independent-reciprocal-equalities/PROOF.md),
  14796 B, SHA256
  d55eb70efa9b5e6b2f52f4c68c44caeb9724b31e7cf16cde0f3cf605414af978,
  explicitly excludes sign inequalities. It remains proved. The difference
  here is ORDER, not another equality or radical-independence argument.

* The completed COMMON-count order/log-zero equivalence
  [G3-ARITH-ROOT-ORDER-LOGZERO-01](https://github.com/Sodelin/Research-Commons/blob/719b8340a0fd72aa18678353c8dbd5a39e42f91f/research/2026-10-23-g3-reciprocal-order-log-zero/PROOF.md),
  13309 B, SHA256
  0a705a550b062879b02f78d38fd379ddd48be9b4c29fe1eee6ce3fbd58b40b5b,
  uses ONE shared integer. It supplies no independent-count order decision
  and is not contradicted by the theorem below.

* The complete old fixed rational-counter screen,
  research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/
  nonlinear-counter-lifts/RATIONAL-REPETITION-COUNT-SCREEN.md,
  6915 B, SHA256
  a21c138332f51f5db48d58374d5745a83b4e896bf585da161729c90761322bd9,
  Git blob 1d863aae43d00c6edd8d44ea87555b0df345cca2.
  It excludes exact polynomial integer values from a fixed rational readout
  of a fixed semisimple word K^n. It explicitly leaves cutpoint-language
  encodings and varying banks outside that screen. Here r_n varies with n;
  the readout only approximates index differences, and a strict language
  threshold is preserved. No exact rational decoder of n or fixed K^n is used.

The local authored audit/continuation archives and the relevant retained
hardness package were searched; matching proof scopes were read. This is a
bounded comparison, not a worldwide priority or exhaustive absence claim.

The classical undecidability input is the Davis--Putnam--Robinson--Matiyasevich
theorem. Martin Davis's primary exposition
[Hilbert's Tenth Problem is Unsolvable](https://www.math.umd.edu/~laskow/Pubs/713/Diophantine.pdf),
American Mathematical Monthly 80 (1973), 233--269, gives integral
Diophantine undecidability in its introduction and the recursively-enumerable
characterization in Section 8, Theorem 8.1. Those statements and the
positive-to-integer conversion were consulted; the entire 38-page proof was
not independently re-reviewed here. Classical integer undecidability and
universal Diophantine polynomials retain their attribution.

Interpretability of arithmetic from discrete real sets also has established
context, including
[Hieronymi, arXiv:0906.4972v2](https://arxiv.org/abs/0906.4972).
Only its abstract statement was inspected here. No existential or
single-inequality conclusion is inferred from that abstract; the explicit
quantitative reduction below proves our precise receiver statement.
Historical novelty of that application is unestablished.

## 3. A rational coordinate with an asymptotically constant index gap

The transformation of a root uses only the rational function

    A(x) = (1+x)/(2(1-x)).

Write c=log 2 and a=1/c FOR THE PROOF ONLY. Neither is an input coefficient.
For real t>=1 put

    f(t) = A(exp(-c/t)) = (1/2)coth(c/(2t)).

In particular A(r_n)=f(n). Elementary estimates give

    2/3 < c < 3/4,             4/3 < a < 3/2,          (1)
    4/3 < f'(t) < 3/2,        f(t) < 2t,             (2)
    a - 1/t^2 <= f'(t) <= a,  f'(t) -> a.            (3)

Here are proofs, so no numerical log estimate is being hidden.

The absolutely convergent expansion

    c = 2 sum_(j>=0) 1/((2j+1) 3^(2j+1))

is greater than its first term 2/3 and smaller than the corresponding
geometric sum 3/4. This proves (1).

With z=c/(2t),

    f'(t) = (1/c)(z/sinh z)^2.

The function z/sinh z is decreasing for z>0: z*cosh z-sinh z is positive,
as its derivative is z*sinh z>0 and its limit at zero is zero. Thus f'
is increasing on t>=1 and tends to a. Since exp(c)=2,

    sinh(c/2)^2=1/8, so f'(1)=2c>4/3.

Together with (1) this proves the derivative part of (2). Since f(1)=3/2,
integrating f'<3/2 gives f(t)<=3t/2<2t.

Finally sinh z>=z. Also the factorial bounds (2j+1)!>=6^j imply

    sinh z/z <= 1/(1-z^2/6),  0<=z<=c/2<1.

Consequently

    (z/sinh z)^2 >= (1-z^2/6)^2 >= 1-z^2/3,
    0 <= a-f'(t) <= c/(12t^2) < 1/t^2.

This proves (3).

An immediate exact discrete consequence is

    5/4 < f(s)-f(t) < 7/4
       if and only if s=t+1,                         (4)

for positive INTEGER s,t. A one-step gap lies between 4/3 and 3/2. A
nonpositive step gives a nonpositive gap, and a step of at least two gives
a gap greater than 8/3. No approximate rounding oracle is used in (4).

## 4. Effective construction from an integer Diophantine polynomial

Let P in Z[X_1,...,X_m] be arbitrary. Select an integer d>=max(2,deg P),
taking deg 0 for the zero polynomial, and define

    H = 1 + sum absolute values of the coefficients of P,
    B = max(64, d H 2^(d+7)).                          (5)

All these quantities are effectively computed from P.

Use m+2 root variables x_0,x_1,x_2,...,x_(m+1). In their A coordinates set

    u = A(x_0),
    h = A(x_1)-A(x_0),
    delta_i = A(x_(i+1))-A(x_0).

Let P^h(delta,h)=h^d P(delta_1/h,...,delta_m/h) denote the degree-d
homogenization, interpreted AS A POLYNOMIAL even at h=0. Put

    F =
      [u^2(1-16(h-3/2)^2)-4B^2] h^(2d)
      -4u^2 [P^h(delta,h)]^2
      -sum_i delta_i^(2d).                           (6)

This is an integer polynomial in the A coordinates:
1-16(h-3/2)^2=-16h^2+48h-35 has integer coefficients. Its total degree
in those coordinates is at most L=2d+4.

To obtain the promised polynomial in the ROOT variables, set

    D(x) = product_(j=0)^(m+1) [2(1-x_j)]^L,
    Q(x) = D(x) F(A(x_0),...,A(x_(m+1))).             (7)

Every denominator is cleared since each individual A degree is at most L.
Thus Q is effectively an INTEGER polynomial, of total degree at most
(m+2)L. At every tuple of the allowed roots, all 2(1-x_j)>0, so D>0 and

    Q(x)>0 iff F>0.                                  (8)

No logarithm, real parameter, irrational coefficient, infinitesimal or
quantifier over a continuous domain is part of the constructed input.

We prove the exact equivalence

    exists v in Z^m: P(v)=0
       iff exists positive integer root indices: Q>0.       (9)

## 5. Excluding zero denominators and false small-index witnesses

At h=0, (6) gives

    F = -4u^2[P^h(delta,0)]^2 - sum_i delta_i^(2d) <= 0.

Thus F>0 AUTOMATICALLY excludes h=0. At h!=0, put V_i=delta_i/h and write

    F = u^2 h^(2d) (1-G),
    G = 4P(V)^2 +16(h-3/2)^2 +(2B/u)^2
                       +sum_i V_i^(2d)/u^2.          (10)

At root tuples u>0, and every term of G is nonnegative. Therefore F>0
implies ALL of

    |P(V)|<1/2,
    5/4<h<7/4,
    u>2B,
    |V_i|^d<u for every i.                            (11)

The second condition also proves h>0.

Write the root indices as t,s,n_1,...,n_m. Then u=f(t). By (2) and (11),

    t>B>=64.

By (4), the calibration index is EXACTLY s=t+1. Define actual integers

    v_i=n_i-t.                                       (12)

They may be positive, zero or negative; n_i itself remains positive.

Since f'>1 on [1,infinity), integration gives

    |v_i| <= |f(n_i)-f(t)| = h|V_i| <= 2|V_i|.

Hence (11), d>=2 and u<2t give

    |v_i| < 2u^(1/d) <= 2sqrt(2t) < t/2.

Every interval between t and n_i is therefore inside [t/2,infinity).

By (3), f' on this whole interval and the calibration average

    h = integral_t^(t+1) f'(w) dw

both lie in [a-4/t^2,a]. Subtracting v_i copies of this average from
the oriented integral from t to n_i gives, also for negative v_i,

    |V_i-v_i| <= 4|v_i|/(h t^2) <= 4|v_i|/t^2.       (13)

The h>1 bound used here is guaranteed by (11). At v_i=0 both sides are
zero. Thus no unproved uniform estimate at tiny n_i is being used: the
range penalty has already forced n_i>t/2.

## 6. Uniform integer-polynomial error bound and soundness

Let R=max(1,|V_1|,...,|V_m|). We have |v_i|<=2R and, from (13),

    max_i |V_i-v_i| <= 8R/t^2,
    R^d <= u < 2t.

On the line segment from V to v, each coordinate has absolute value at
most 2R. The sum of absolute partial derivatives of any monomial of
degree at most d is at most d(2R)^(d-1). The mean-value inequality and
the definition of H consequently give

    |P(V)-P(v)|
       <= H d (2R)^(d-1) * 8R/t^2
       = H d 2^(d+2) R^d/t^2
       < H d 2^(d+3)/t
       < 1/16,                                      (14)

where t>B and (5) were used. This also covers constant/zero polynomials.

But P(v) is an INTEGER and (11),(14) imply |P(v)|<1/2+1/16<1.
Therefore P(v)=0. This proves the backward implication in (9) for
EVERY possible root-index tuple, not merely for a prepared large one.

## 7. Completeness with finite count witnesses

Conversely suppose v in Z^m and P(v)=0. Choose positive integers t tending
to infinity, set s=t+1 and n_i=t+v_i. All n_i are positive once t is large.

From (3) and the integral formulas,

    h=f(t+1)-f(t) -> a,
    V_i=[f(t+v_i)-f(t)]/h -> v_i,
    u=f(t) -> infinity.

Thus in (10) all terms except the calibration term tend to zero, and

    G -> 16(a-3/2)^2 < 4/9 < 1,

by (1). For every sufficiently large FINITE t we have G<1, hence F>0
and Q>0. This proves the forward implication in (9).

Only existence of a finite integer witness was needed. No infinite root
index, actual limiting root x=1 or fractional factor count is admitted.

Equations (5)--(9) give an effective many-one reduction from integral
Diophantine feasibility. Classical DPRM therefore proves undecidability.

## 8. Semidecision, fixed-complexity and stopping consequences

A candidate count tuple is exactly checkable: each root is a specified
positive real-algebraic number, and the integer polynomial sign is decidable.
Enumerating all count tuples therefore semidecides YES.

DPRM gives a fixed Diophantine polynomial U(e,z) for any chosen
recursively-enumerable complete set, after the standard conversion from
positive to integral auxiliary variables. For the specialization P_e(z),
the number m of variables and a degree upper bound d are fixed. Only the
integer coefficients and hence H,B vary effectively with e.

Our construction then has FIXED K=m+2 root variables and degree bounded by
the FIXED D=K(2d+4). This proves recursively-enumerable completeness and the
fixed-K,D corollary, without claiming an optimal numerical universal pair.

If a total computable one-witness bound N(Q) existed, checking all count
vectors with each coordinate <=N(Q) would decide the problem. The bound
would have to be defined on NO inputs too. Thus no such bound exists.
Likewise, an effective sound complete finite NO certificate system,
together with the YES enumeration, would decide the problem by dovetailing;
no such unrestricted system can exist.

This is a statement about ONE witness and total NO, not a mistaken demand
to bound all equivalent presentations.

## 9. Exact delta and original G3 boundary

The ZERO/NONZERO arithmetic branch remains decidable. ORDER with a COMMON
count retains its completed equivalence to homogeneous-log zero. The
unrestricted INDEPENDENT-count ORDER branch is now classified negatively.
There is no conflict: calibration and each shifted index are independent.
Forcing all root variables to share one count makes h=0, which this
construction explicitly rejects.

The old fixed-word rational readout exclusion also remains intact. The
new proof does not output the integer n by a rational function of one
fixed source word K^n. It uses varying reciprocal roots, auxiliary
calibration indices, approximate index differences and a robust cutpoint
inequality. Those are precisely different quantifiers/interfaces.

For original G3, this rules out filling a gap by an UNRESTRICTED total
solver for arbitrary polynomial order constraints on independent fixed-base
reciprocal powers. It does not rule out a source-specific decidable fragment,
a different normal form, or an input-derived source bound proved using
additional structure.

In particular, the fixed rational base and independently indexed roots
here are ARITHMETIC data, not supplied physical cells. No theorem says
every fitting original source must follow this encoding. No unbounded
fresh-position parameter tie, extra observable, refreshed COMMON bank,
new calendar equality or all-core alphabet enforcement is introduced.

The actual original forward AND converse source correspondence, joint
COMMON/I/BOTH rows on one bank, original IDs/ordered parents, protected
menus, chronology, opaque subtrees and unbounded ancestral completion
remain requirements of G3. Without a source-faithful two-way transfer,
this arithmetic theorem is NOT G3 undecidability or original goal closure.

One next original-goal action is to characterize the ACTUAL restricted
count-order constraints delivered by a source-complete reduction, rather
than propose the now-excluded universal arithmetic backend. No such
source-complete restriction or new full G3 mechanism is claimed here.
Existing owners, no local Git/no subagents and all held/USED/UNKNOWN
actions remain. Proof authoring selects no new scientific/build/model job.
