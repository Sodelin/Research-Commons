# Exact chronological charge balance on the active commutator fibre

Stable key: G3-ACTIVE-CHARGE-BALANCE-01.
24 October2026UTC. Existing G3 owner.

**PROVED BY HAND:** the source constraints below, as derived applications
of the OLD four-root quotient and the already completed S-reference.
Author self-review complete; independent correctness review and Lean
formalization unperformed. Historical novelty is unassessed. No new
source coefficient, quotient, engine, cap ladder or executed tuple.

This applies DIRECTLY to the active AG-Pair fibre, with arbitrary strict
coins, relative scales and finite word lengths. It does not use the
different critical calibration D=sqrt(C). It bounds a SIGNED-CHARGE
DIFFERENCE; the positive charges can cancel. It is not the missing
source-variance/index theorem or original G3 closure.

## 1. Original source scope and reused quotient

Take the actual chronological equal-arm private word

    K=E(z0) B(q1,q1,g1) E(z1) ... B(qN,qN,gN) E(zN),

with every parameter in(0,1). Each cell has a distinct fresh natural
bit, original parent0 probability g_i and native gamma_i=1-g_i.
INDEPENDENT routing is by CURRENT root, followed by opaque grafting.
The SAME physical tuple supplies COMMON and I. The complete forest
commutation below is an internal necessary consequence of the existing
original input/source reduction, not a new hidden observation.

Use the OLD complete four-input unranked labelled-forest quotient.
To avoid confusing its signed C-coordinate with COMMON passage c,
write

    k_j=b_j(K_I),  j=2,3,4,
    x(K)=the OLD C(K),
    y(K)=the OLD C(K)+H(K).

Thus x is the two-cherry/two-root excess over one third of the two-root
total. The old H is the completed balanced-tree excess over one third
of the one-root total. For chronological multiplication P then Q,

    x(PQ)=b2(Q)x(P)+b4(P)x(Q),
    y(PQ)=y(P)+b4(P)y(Q).                            (1)

Every ordinary factor has x=y=0. A bare bigon has H=0, so its x and y
are the SAME signed charge. These facts are OLD, with full opaque-root
chronology; no independent fitting of quotient coordinates is allowed.

## 2. Exact commutator constraints; the endpoint is not zero

Reuse the actual active reference

    q=t/(2-t), b=t^2(2-t),
    S(t)=E(t) B(q,q,1/2) E(b),        0<t<1,
    h=-log t.

Write s_j=b_j(S). Full capped commutation K_I S=S K_I at ANY existing
cap M>=4 implies equality in(1). Hence EXACTLY

    x(K)=(k2-k4)*x(S)/(s2-s4),
    y(K)=(1-k4)*y(S)/(1-s4).                         (2)

All denominators are positive. In particular k4<k2<1: no merger among
four current roots implies no merger of a selected pair, and positive
ordinary factors make the inequality strict. No higher k_j has been
identified with s_j^nu or with an ordinary diagonal.

The OLD equal-arm bare charge, with v=g(1-g), beta=1-4v,d=1-q, is

    chi(q,g)=(2/3)v*d^2*((1-2v)d-3beta)
            =(1/3)v*d^2*[d-(6-d)beta].              (3)

At g=1/2 this is d^3/12. Applying the OLD positive pad law gives

    x(S)=(2/3)*t^8*(1-t)^3/(2-t)^2,
    y(S)=(2/3)*t^6*(1-t)^3/(2-t)^3,
    s2=t^3.                                        (4)

These are direct substitutions into the retained quotient and reference,
not newly generated source coefficients. Both coordinates in(4) are
STRICTLY POSITIVE. They are not ordinary-return zero endpoints.

At four roots, each equal-arm routing has at least two same-arm pairs,
so b4(B(q,q,1/2))<=q^2. The ordinary pad product is t*b=t^3(2-t).
Consequently

    s4<=(t*b)^6*q^2=t^20*(2-t)^4<=t^16,             (5)

where t(2-t)<=1. Therefore

    s2-s4>=t^3*(1-t^13)>=t^3*(1-t),
    1-s4>=1-t^16>=1-t.

Combining(4)--(5) and1-t<=h proves the uniform, all-length bounds

    0<x(K)<=(2/3)*(k2-k4)*h^2,
    0<y(K)<=(2/3)*(1-k4)*h^2.                       (6)

The comparison uses actual commutation, not only the pair data.

## 3. TWO exact chronological source-moment balances

For cell i set

    d_i=1-q_i, v_i=g_i(1-g_i), beta_i=(2g_i-1)^2,
    alpha_i=z0^6*product_(j<i)[b4(B_j)*z_j^6],
    rho_i=z_i*product_(j>i)[b2(B_j)*z_j].

These are the OLD ACTUAL chronological weights. They are positive,
at most1, and rho_i strictly increases with i. No factor is reordered.

Let w_(0,i)=alpha_i,w_(1,i)=alpha_i*rho_i. Define two pairs of
NONNEGATIVE source sums, for j=0,1,

    P_j=sum_i w_(j,i)*v_i*d_i^3,
    B_j=sum_i w_(j,i)*v_i*(6-d_i)*beta_i*d_i^2.       (7)

The symbols P_j here are literal weighted source sums, not root-count
probabilities, the earlier rounding P3, or newly acquired observations.
The old full chronological expansion and(3) give EXACTLY

    P_1-B_1=3x(K),
    P_0-B_0=3y(K).                                  (8)

Thus every actual word in the ACTIVE commutator fibre satisfies

    0<P_1-B_1<=2*(k2-k4)*h^2,
    0<P_0-B_0<=2*(1-k4)*h^2.                        (9)

Now retain its SAME prescribed COMMON/I pair budget:

    c=2^(-1/m), H=-log c,
    k2=c^(3/4), K_COMMON=E(c).

The OLD no-merger bound gives k4>=c^6. Directly, each bare four-root
no-merger diagonal is at least q_i^6, and ordinary factors are exact.
Since e^(-a)-e^(-b)<=b-a for0<=a<=b,

    k2-k4<=c^(3/4)-c^6<=21H/4,
    1-k4<=1-c^6<=6H.

In particular(9) implies

    0<P_1-B_1<=2*min(1,21H/4)*h^2,
    0<P_0-B_0<=2*min(1,6H)*h^2.                    (10)

Counts, coins, cell scales and placements remain arbitrary. The two
differences are bounded; their separate positive summands are not.

## 4. A genuine weighted-bias constraint, with no pointwise margin

Because each q_i>=c, one has6-d_i>=5+c. Also both actual weights in(7)
are at least c^6. For alpha_i use the OLD b4-prefix bound. For
alpha_i*rho_i use b4(prefix)>=C_prefix^6,
b2(suffix)>=C_suffix>=C_suffix^6 and
C_prefix*C_suffix=c/q_i>=c. Thus no weight lower bound depends on N.

Equations(8)--(9) show B_1<P_1. Hence, without a new source hypothesis,

    sum_i v_i*beta_i*d_i^2
        <=c^(-6)/(5+c)*sum_i v_i*d_i^3.             (11)

Writing a_i=-log q_i for ACTUAL cell exposures, d_i>=c*a_i and d_i<=a_i.
Consequently

    sum_i v_i*beta_i*a_i^2
        <=c^(-8)/(5+c)*sum_i v_i*a_i^3.             (12)

For delta=max a_i the mean beta_i under weights v_i*a_i^2 is therefore
at most c^(-8)*delta/(5+c). All weights are positive. This is a true
source consequence of commutation on the active fibre. It does not
assert delta is small in the REFERENCE h, or that all original coins
are fair/interior. Rare coins naturally carry small v_i.

There must be at least ONE cell with chi_i>0, since both endpoint
charges are positive. Equation(3) then gives, for that cell,

    beta_i<d_i/(6-d_i).

This is an existence statement about a cell, not R9's whole-word
pointwise coin-window premise, a bound on every source presentation,
or a finite witness selector.

## 5. Precise remaining gap and old no-go boundaries

The acquired relations are(8)--(12). They are NOT

    P_j=O(h^2), B_j=O(h^2), max_i a_i=O(h),
    V_h=sum ell_i*(ell_i-h)^2=O(h^5),

nor any integer-index conclusion. Positive P_j and B_j may cancel;
smallness of their difference cannot be substituted for coercivity.
The logarithmic pair gaps ell_i still obey the OLD exact sum ell_i=L.
No endpoint descent of V_h is assumed.

The active endpoint has unknown higher diagonals k_j, with k4 explicitly
retained in(2),(9). It is not an ordinary return. The separate OLD
9/7/6/4 storage Psi also has its already recorded NONZERO boundary on
valid S(t)^N. No boundary term is discarded in this argument.

The different critical-pair admission at D=sqrt(C),11918B/SHA6fae7041,
is not used. The current pair calibration remains c,c^(3/4), and the
source/ID/menu/register/current-root/opaque-graft contracts of the
completed original all-core reduction are unchanged. The result passes
to its actual main-word consequence without adding an original query.

This is an exact derived application to the existing full-scope attempt,
not a new complete attack, global nonnegative additive/PSD cocycle,
all-copy word reconstruction, source-count theorem or G3 endpoint.
The ONE active implication remains AG-Pair (or a genuinely superseding
source disproof); its optional ONE-witness V_h estimate is still unproved.

## 6. Exact predecessor/successor custody and verification scope

The actual prior comparison was recorded BEFORE this source write.
COMPLETE bodies were reread at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:

* [FOUR-ROOT-PLACEMENT.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md),
  12087B/SHA2565f1a25f7a1929f98c25a4223d7d68f4af7e5f9614c62105878292422dde147d9,
  blobc10623a7103c8c478a9644d12aaa9229b59190d1.
  Its exact full quotient and multiplication are OLD/PROVED/REUSE.
* [JOINT-MODE-FULL-FOREST-GUARD-AUDIT.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt4/JOINT-MODE-FULL-FOREST-GUARD-AUDIT.md),
  7792B/SHA2568c11f4a422527e0d5a4d2a71835f40f303c3dfc652309bb549456e1a07ed91bc,
  blobf5af03bbaea87c6509ba72b03af7452e50fe294a.
  Its chronological weights, all-coin charge signs and bare formula
  are OLD/PROVED/REUSE, not new coefficient discoveries.

The completed pair-calibrated addendum14111B/SHA2babce31 atd0b46e3e,
uniform matrix/source minorization, active rounding15350B/SHA1f9ed529,
and later critical admission11918B/SHA6fae7041 were compared at their
actual statement/source boundaries. None was silently promoted to an
ordinary target or a pointwise fairness condition.

The local current/archived audit/continuation search is a bounded
comparison, not historical priority or absence evidence. One first
read-only lookup used the wrong old directory and returned exit128;
ls-tree located the exact g3-witness-bound/attempt4 source, which was
then read completely. No failed lookup was treated as an open theorem.

Author hand proof/self-review are complete for the displayed necessary
constraints. Source reading/hash checks are not fresh kernel execution,
independent whole-chain adoption or Lean formalization. No original
compiler, numerical/symbolic control, solver, native/model/CI job or
old producer ran. Existing owners, native-controller UNBOUND, all
held/USED/UNKNOWN stops, one featurectl identity, no-subagent/no-local-Git
and encryption-before-runtime-persistence restrictions remain.
