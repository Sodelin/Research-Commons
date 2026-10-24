# Power-accurate root grids suffice for the original G3 negative reduction

Stable key: G3-ASYMPTOTIC-ROOT-GRID-REDUCTION-01.

24 October2026UTC. Existing G3 owner, Codex/OpenAI.
**PROVED BY HAND:** the arithmetic robustness theorem and its CONDITIONAL
original-source transfer. **UNPROVED:** the source-specific grid hypothesis
in Section6. Independent correctness review and Lean formalization are
separate and have not been performed. No scientific/source producer,
coefficient control, solver/QE, model/native/compiler/Lean/build job ran.

This paper weakens the missing premise of the EXISTING full-scope attack.
It is not a second attack, a new source wrapper, a physical count theorem
or original G3 closure. The earlier exact CP-Pair is a sufficient stronger
special case; it is not reopened as a second active project.

## 1. Exact predecessor/successor comparison

The COMPLETE retained [independent-root ORDER proof](https://github.com/Sodelin/Research-Commons/blob/b258bd5078e5b841908dc5284879d4de9f348f05/research/2026-10-23-g3-independent-root-order-nogo/PROOF.md),
16206B/SHA2564c54e60bd5466269375a10f260e994d0837954f7b5704016b105e400cce05f05,
was reread, including its explicit error/range guards and fixed-complexity
corollary. Its robust cutpoint mechanism is OLD/PROVED/REUSE. It already
reduces integral Diophantine feasibility to one strict integer-polynomial
inequality on independent roots of1/2. No new undecidability input or
root-order backend is claimed here. Classical DPRM retains its attribution
and primary reference in that proof.

The original-input [all-core source reduction](https://github.com/Sodelin/Research-Commons/blob/26898807efa9d09b632922a2cb47e500ff1df42f/research/2026-10-24-g3-all-core-commutation-reduction/PROOF.md),
31399B/SHA2563c7d37379c88d27c43c044454746ef4d0b8722872d2e6bcb69a5af6021c15693,
and its later [pair-calibrated successor](https://github.com/Sodelin/Research-Commons/blob/d0b46e3eeba37d61144c0008e994cbdd053434ad/research/2026-10-24-g3-pair-calibrated-reference/PROOF.md),
14111B/SHA2562babce31b4043acb18c7d2a19a75a92d5eb8320b0f705f4283a19132996b91c9,
are PROVED BY HAND and reused unchanged. They supply the original all-core
converse, legal passive coefficient channel, auxiliary field bank, strict
witness construction and SAME original tuple. They do not prove CP-Pair.

The later [paired-diagonal application and attribution correction](https://github.com/Sodelin/Research-Commons/tree/d315068224c12dc741798107bb4b558ec66f2888/research/2026-10-24-g3-weak-equal-arm-paired-diagonals)
were compared at their actual scope. Their OLD interior-coin source
rule and fixed COMMON/I diagonal synthesis are completed suppliers.
Off-diagonal/commutation control is absent. The old all-copy ordered
normal form is also completed; it does not give a finite unknown-length
detector. Neither is being reopened or silently upgraded here.

Local authored audit/continuation archives and handoffs were searched for
approximate-integer/root-grid, quantization, robustness and index-error
aliases before this extension. The actual prior proof, not an empty search,
supplies the positive comparison above. This is not an exhaustive absence
or historical priority claim.

**Precise delta.** The old proof assigned EXACT integer indices. Here each
real index may differ from some integer by A times a fixed negative power
of that real index. A larger polynomial RANGE penalty absorbs those errors
while the integer-polynomial gap remains1. This is an application/extension
of the old robust construction. No physical estimate is inferred from it.

## 2. Arithmetic theorem and domain

For x in(0,1), define only in the mathematical proof

    nu(x)=log(1/2)/log x,
    Acoord(x)=(1+x)/(2(1-x)).

No logarithm or index is an input coefficient or an observable.

Fix integers A>=1,k>=1,T>=2. Let X be ANY subset of(1/2,1) with:

* every exact root r_N=2^(-1/N) belongs to X for all sufficiently large
  integers N;
* whenever x belongs to X and nu(x)>=T, there is an integer n with

      |nu(x)-n| <= A*nu(x)^(-1/k).                    (AG-arith)

No effectivity, closedness or independent membership test for X is assumed.
The following is an effective reduction for each fixed A,k,T:

**Theorem.** Given any integer polynomial P, one can compute one integer
polynomial Q such that

    exists v in Z^ell with P(v)=0
      iff exists x_0,...,x_(ell+1) in X with Q(x)>0.   (1)

The SAME Q works for every X obeying the two promises. In particular,
an algorithm deciding this feasibility relation for any such fixed X
would decide integral Diophantine feasibility.

A bound A*nu^(-beta) for ANY fixed beta>0 suffices: choose an integer
k with1/k<=beta and increase A to an integer. Restricting to nu>=1
only weakens that bound. No optimization of the exponent is needed.

The statement remains conditional on X's promises. It does not assert
that an actual source satisfies them. Nor does it assert enumerability
of an arbitrary abstract X.

## 3. Construction: reuse the old cutpoint, strengthen its range penalty

Write lambda=log2 and a=1/lambda FOR THE PROOF. Set

    f(t)=Acoord(exp(-lambda/t))=(1/2)coth(lambda/(2t)).

The OLD proof Section3 establishes, for ALL real t>=1,

    4/3 < f'(t) <3/2,
    f(t)<2t,
    a-1/t^2 <= f'(t) <=a,
    4/3<a<3/2.                                      (2)

Those explicit elementary bounds are reused, not rederived.

Given P in Z[X_1,...,X_ell], choose

    e=max(1,degree P), with degree0 for constants;
    d=2*k*e;
    H=1+sum absolute values of P's coefficients;
    L=64*A*H*e*2^e;
    B=max(64,2*T,(128*A)^k,(16*L)^(2*k)).             (3)

All quantities in(3) are positive integers, effectively computed from P
and the fixed constants. Put

    u=Acoord(x_0),
    h=Acoord(x_1)-Acoord(x_0),
    delta_i=Acoord(x_(i+1))-Acoord(x_0),
    P_h(delta,h)=h^d*P(delta_1/h,...,delta_ell/h),

where P_h is its polynomial homogenization, also at h=0. Use exactly the
OLD cutpoint pattern

    F=[u^2*(1-16*(h-3/2)^2)-4*B^2]*h^(2*d)
         -4*u^2*P_h(delta,h)^2-sum_i delta_i^(2*d).    (4)

It is an integer polynomial in the Acoord variables since
1-16*(h-3/2)^2=-16*h^2+48*h-35. Its total degree is at most J=2*d+4.
Clear denominators by

    Q(x)=product_(j=0)^(ell+1)[2*(1-x_j)]^J
              *F(Acoord(x_0),...,Acoord(x_(ell+1))).  (5)

Every denominator is positive on X. Q is an effectively obtained integer
polynomial of degree at most(ell+2)*J, and Q>0 iff F>0. There is no
approximate-root sign computation or logarithmic input relation in(5).

At h=0, F<=0. At F>0 define V_i=delta_i/h and
R=max(1,|V_1|,...,|V_ell|). Dividing(4) gives the OLD exact identity

    F=u^2*h^(2*d)*(1-G),
    G=4*P(V)^2+16*(h-3/2)^2+(2*B/u)^2
                                      +sum_i V_i^(2*d)/u^2.

Thus every possible witness, not just a prepared one, satisfies

    |P(V)|<1/2,       5/4<h<7/4,
    u>2*B,           R^d<=u.                         (6)

The last inequality includes R=1 because u>2*B>1.

## 4. Soundness for every near-grid witness

Let the real indices of x_0,x_1,x_(i+1) be t,s,t_i. All exceed1
because X is a subset of(1/2,1). From u=f(t)<2t and(6),

    t>B.                                             (7)

By the mean value theorem and(2),(6),

    5/6<s-t<21/16,
    |t_i-t| <=(3/4)*|delta_i|
               <(21/16)*R
               <=(21/16)*sqrt(2t)<t/2.              (8)

The last step uses d>=2 and t>64. The calibration index s is also between
t/2 and2t. Hence ALL indices in this tuple are greater than t/2>T and
AG-arith applies to them.

Choose integers n_0,n_1,n_(i+1) and errors

    t=n_0+epsilon_0,
    s=n_1+epsilon_1,
    t_i=n_(i+1)+epsilon_(i+1).

Every error has absolute value at most

    E=2*A*t^(-1/k)<1/64,                             (9)

by(3),(7),(8). From(8),(9), n_1-n_0 is an integer strictly between
5/6-1/32 and21/16+1/32. Its ONLY possible value is1. Define the
actual integers

    v_i=n_(i+1)-n_0,
    sigma=s-t=1+eta,       |eta|<=2*E,
    t_i-t=v_i+theta_i,     |theta_i|<=2*E.            (10)

Equation(8) gives |v_i|<2R. On every interval used here, f' differs
from a by at most4/t^2. In oriented integral form this gives

    |delta_i-a*(t_i-t)| <=4*|t_i-t|/t^2,
    |h-a*sigma| <=4*sigma/t^2 <=8/t^2.

Subtract v_i times the second integral from the first and use
(t_i-t)-v_i*sigma=theta_i-v_i*eta, a<3/2 and h>1. The resulting
explicit bound is

    |V_i-v_i|
       <=9*E*R+24*R/t^2
       <=64*A*R*t^(-1/k).                            (11)

For clarity, the first two derivative-error terms sum to less than
(4*(21/16)+16)*R/t^2<24*R/t^2; the index-error term is at most
(3/2)*2E*(1+2R)<=9ER. Thus(11) holds uniformly in all indices,
including negative or zero differences v_i.

On the segment between V and v, every coordinate has absolute value at
most2R. The old monomial mean-value estimate, now with degree e, yields

    |P(V)-P(v)|
       <=H*e*(2R)^(e-1)*64*A*R*t^(-1/k)
       =64*A*H*e*2^(e-1)*R^e*t^(-1/k).

Since d=2ke and R^d<=u<2t,

    R^e<=(2t)^(1/(2k))<=2*t^(1/(2k)).

Consequently

    |P(V)-P(v)| <=L*t^(-1/(2k))<1/16,              (12)

by(3),(7). P(v) is an INTEGER. Equations(6),(12) give
|P(v)|<1/2+1/16<1, so P(v)=0. This proves soundness for EVERY
near-grid witness allowed by X; a small-index or wrong-calibration
witness cannot bypass the guards.

## 5. Completeness, fixed complexity and exact role of robustness

If P(v)=0 for some integer tuple v, choose integers n tending to infinity
and use the EXACT roots with indices n,n+1,n+v_i. All lie in X once n
is sufficiently large. The OLD completeness argument applies unchanged:
u tends to infinity, V tends to v, h tends to a, and

    G tends to16*(a-3/2)^2<4/9<1.

Every sufficiently large FINITE n therefore gives Q>0. Only finite
indices, strict roots and a finite tuple are used.

This proves(1). For a fixed universal Diophantine polynomial, ell and e
are fixed; A,k,T are fixed constants of the hypothesized source. Hence
the number of root variables and degree(ell+2)*(4ke+4) stay FIXED.
Only coefficients, particularly B, depend effectively on the instance.
This remains one strict polynomial inequality, with the same fixed base.

The construction needs a power-vanishing index error, not equality of
the index to an integer. It does NOT show that a fixed nonvanishing
error tolerance or a noneffective convergence rate suffices. It does
not round a source's actual number of cells, and it makes no claim that
the selected integer equals every presentation's length.

## 6. The weaker source hypothesis AG-Pair: still UNPROVED

Reuse the completed strict reference

    S(t)=E(t)*B_I(t/(2-t),t/(2-t),1/2)*E(t^2*(2-t)).

Here E denotes ordinary population passage by its survival parameter.
The SAME physical tuple has COMMON pair t^4 and I pair t^3.
Original parent0 probability is g; native parent1 is gamma=1-g.

**AG-Pair.** There exist FIXED integers

    m>=1, M>=4, A>=1, k>=1, T>=2

such that, with c=2^(-1/m), EVERY c<t^4<1 and EVERY finite strict
equal-arm private word K, of arbitrary unknown length and arbitrary
strict coins, satisfying

    K_COMMON=E(c), b2_I(K)=c^(3/4),
    [K_I,S(t)]=0 on the COMPLETE forest carrier through M,

obeys, whenever

    nu=log c/(4*log t)>=T,

the source-specific estimate

    dist(nu,Z) <= A*nu^(-1/k).                       (AG-Pair)

The numerical constants and forest cap are fixed BEFORE the input. There
is no relative-scale, fair-coin, fixed-cell-count or chart-regularity
promise. This is about a scalar inferred from the actual source/reference
pair, not an independent real variable licensed as a source actuator.

AG-Pair is NOT proved in this paper. No finite jet span, mere absolute
Taylor remainder, synthetic fractional power or algebraic centralizer
is asserted to supply it. It is the ONE active missing source premise of
this route. Exact CP-Pair implies it, but exact CP-Pair is stronger than
this reduction requires and is now only an inactive sufficient special
case. Failure of exact CP-Pair alone would not refute AG-Pair.

Conversely, for EVERY integer N>=2, the actual strict word S(t)^N at
t=c^(1/(4N)) satisfies all premises and has nu=N. This is the old physical
reverse witness, with no fractional count or new source constructor.

## 7. Conditional transfer to the FULL original G3 input

Assume AG-Pair for the fixed constants in Section6. Define X to be the
set of y=t^(4m) for which SOME actual finite strict word K satisfies
that section's exact source/commutation premises. Different variables
may choose different actual words; each uses one tuple in ALL its rows.
Then

    y=2^(-1/nu),       nu=log c/(4*log t)>1.

All sufficiently large exact roots belong to X by S(t)^N, and AG-Pair
is precisely AG-arith for this X. Sections2--5 therefore reduce integral
Diophantine feasibility to one polynomial inequality Q(y)>0 over X.

Apply the ALREADY PROVED pair-calibrated original-input construction
to the polynomial

    Q_m(z_0,...,z_(ell+1))=Q(z_0^m,...,z_(ell+1)^m),
    with z_j=t_j^4.

It produces an original finite rational/effectively real-algebraic joint
input with an original source iff those actual words and that inequality
exist. This is EXACTLY its established all-core equivalence, not a new
claim that an arbitrary graph follows a hand-modeled grammar.

The source map and its converse preserve:

* all unknown finite original binary rooted-LSA, outer-labelled planar,
  cut-child galled cores and parallel original arc occurrences;
* one finite strict source, its original IDs/ordered parents and ONE
  natural tuple for every supplied COMMON/I/BOTH row and original control;
* actual equal-arm word extraction on the calibrated main slots, actual
  auxiliary placement/sole-cell forcing, fixed/read-only menus and the
  finite original physical polynomial relations;
* natural register sharing, per-CURRENT-root independent routing,
  chronological populations, opaque prior trees, the original topology/
  passive channel readout and infinite ancestral completion.

No unbounded fresh-position parameter tie, hidden register query,
configuration-aware channel, extra log/calendar equation, physical
inverse, repeated unknown-box observation or whole-template promise is
added. c and c^(3/4) are effectively algebraic constants for the fixed m;
the actual input coefficients and channel construction are effective.

Thus, CONDITIONAL ON AG-Pair, original G3 is undecidable. In particular,
there is no total input-computable bound on ONE admitted finite witness,
defined also on NO inputs, and no total terminating-NO recognizer.
YES is still exactly checkable/enumerable by the retained fixed-source
semialgebraic procedure. This is an original-source impossibility
alternative, not a proposal to bound all equivalent presentations.

Without AG-Pair, none of those original negative conclusions is proved.

## 8. Changed frontier and evidence boundaries

COMPLETED/REUSE: old integer-gap arithmetic, original all-core forcing,
pair-calibrated strict reference, reverse integer powers, all-copy
normal form, fixed COMMON/I paired-diagonal synthesis and its old
interior-coin provider.

COMPLETED HERE BY HAND: robustness for a power-accurate root grid and
the conditional original-source reduction using it. This is an explicit
extension of the old guarded arithmetic proof, not another new backend.

ONE UNSUPPLIED IMPLICATION: AG-Pair for actual arbitrary-length positive
words at some fixed finite forest cap. The original full G3 recognition/
NO goal remains ACTIVE and unresolved. Exact CP-Pair is retained intact
as a stronger sufficient statement, not a second work queue. All-core
source/observer binding is already proved and must not be rebuilt.

One existing next action is a source-derived, all-length asymptotic
index estimate or a materially superseding disproof, retaining arbitrary
strict coins, tiny cells and fixed total budget. No cap/degree ladder,
another arithmetic solver, source factory or new scientific job follows.

Authored source, independent acceptance, Lean formalization, publication,
recipient reading and original goal closure remain separate. No local Git
mutation, subagent/chat, turn wake/start/resume/interrupt, native writer
bypass or held/USED/UNKNOWN replay occurred. Private runtime remains
memory-only or encrypted before persistence with the ONE existing identity.
