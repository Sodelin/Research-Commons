# Uniform quadratic projection of capped reference commutants

Stable key: G3-UNIFORM-ORDINARY-COMMUTANT-ESTIMATE-01.

24 October2026UTC. Existing G3 owner, Codex/OpenAI.
**PROVED BY HAND**, author self-review complete; independent correctness
review and Lean formalization have not been performed. No scientific
source/coefficient/numerical/solver/QE/model/native/compiler/build job ran.

This is a quantitative MATRIX component of the existing full-scope G3
attempt. It does not prove the inferred integer-index estimate AG-Pair,
a source count bound, physical factorization or original G3 closure.
Classical spectral projection and the OLD source lift are reused.

## 1. Exact carrier and theorem

Fix ANY finite cap M>=2. Use the COMPLETE labelled unranked binary-forest
carrier on M original current-root tokens, including its lower-current-
root strata. Previously formed subtrees are opaque and grafted intact.
A same-count transition is the literal identity on that input forest.
Population/register updates with no merger are outside this smaller
private operator contract. An isolated empty-input identity can be added
without changing anything.

Use row-stochastic matrices in chronological composition and the maximum
absolute row-sum norm. Q is the ordinary pair-rate-one coalescent generator.
For a forest with r roots its diagonal is -lambda_r, lambda_r=binom(r,2).
Every unordered root pair merges at rate1. Write

    E_h=exp(h Q),          Lambda=binom(M,2), L=2*Lambda.

Thus ||Q||<=L, and every positive E_h has norm1.

For0<t<1 reuse the actual strict source

    S(t)=E(t) B_I(t/(2-t),t/(2-t),1/2) E(t^2*(2-t)),

where E(v) in this display means the ordinary survival-v kernel
exp((-log v)Q). Put h=-log t. Its original parent0 coin and native
parent1 complement are both1/2. This is the SAME previously constructed
physical reference, not a replacement generator.

Define rational/effective constants

    h_M=1/(32*L^2),
    C_M=6*L^3*M*(M-1)*(6*L+4)*(3*L+2)^(M-2).        (1)

Let K be ANY stochastic count-triangular forest kernel whose r-root
diagonal block is k_r I,0<=k_r<=1,k_1=1. In particular every actual
private positive word of arbitrary finite length/coins/scales satisfies
this condition. Assume its capped matrices satisfy

    K S(t)=S(t) K,       0<h<=h_M.

Let P_r(Q) be the ordinary generator's spectral projectors. Then

    K_0=sum_(r=1)^M k_r P_r(Q),
    [K_0,Q]=0,
    ||K-K_0|| <= C_M*h^2.                            (2)

The constants depend ONLY on M, not K's architecture, parameter margins,
length, higher diagonal values or COMMON budget. The labelled forest-
shape count does not enter them.

K_0 has the SAME no-merger diagonals k_r and row sums1. It is an algebraic
comparison operator; positivity, physical realization and representation
as a mixture of ordinary populations are NOT claimed. Pair calibration
alone does not identify it with an ordinary E_h or a fractional S power.

## 2. Prior comparison: exact reused and additional claims

The existing pair-calibrated reference is PROVED at
[d0b46e3e](https://github.com/Sodelin/Research-Commons/blob/d0b46e3eeba37d61144c0008e994cbdd053434ad/research/2026-10-24-g3-pair-calibrated-reference/PROOF.md),
14111B/SHA2562babce31b4043acb18c7d2a19a75a92d5eb8320b0f705f4283a19132996b91c9.
Its pair calibration, original all-core caller and all-copy scope are
reused. The later asymptotic-grid arithmetic extension4697d8e3 does not
provide an actual matrix or integer-index estimate.

The completed [projective spectral theorem](https://github.com/Sodelin/Research-Commons/blob/0dbc43330c11fcc2361c016135cd71760e00d578/research/2026-10-23-g3-projective-spectral-bound/PROOF.md),
G3-PROJECTIVE-SPECTRAL-01,18659B/SHA256
9aeaccb27b4979a103ec7adb6e9e5f3483b80ebaf9b553f135090c75e600ca7d,
already supplies boundary semisimplicity and uniform M! projectors.
Its exact finite private carrier and existing strict-source predecessor
are reused; this is not a new semisimplicity or generic interpolation
theorem. The classical triangular centralizer calculation already used
in the current source ledger is also reused.

The COMPLETE OLD source lift was reread at Commons8b96f4fb:
research/2026-10-08-dot-g4-positive-composition-attempt-1702z/
POSITIVE-COMPOSITION-CUBATURE-AND-SOURCE-LIFT-FAILURE.md,
18106B/SHA2569c7262726a95dc7631fe74a3437befab2869fd3025e042a983b3ba1cadc993af.
It keeps the actual recolouring projection between cells, and does NOT
make a bare bigon a flow. The second-order calculation below is a direct
application of this OLD lift and actual fair pair clock; no new all-order
source-coefficient discovery is asserted.

Local current/audit/continuation archives and the existing G4 sources
were searched for commutant/projector perturbation and quadratic-distance
aliases. The closest retained conclusions above were read at their stated
scope. This is not a worldwide historical novelty claim.

Additional claim here: a fixed effective quadratic error for the WHOLE
capped commuting kernel, uniformly in arbitrary positive word length,
without fixing its higher no-merger diagonals or substituting a physical
inverse. The estimate is matrix geometry, not the missing positive-word
phase theorem.

## 3. Fair equal-arm source expansion on the full forest carrier

Let J route EACH CURRENT root independently to two colours with fair
probability1/2. Let D forget colours and pool the forests, retaining their
genealogies. These rectangular stochastic row kernels satisfy JD=I.
Let G coalesce pairs only within each colour at rate1. It satisfies
||G||<=L, and its positive semigroup has norm1.

For equal arm EXPOSURE u,

    B(u)=J exp(uG) D.

This is the row-kernel orientation of the retained column lift.
It has the actual current-root routing, retained same-colour merger law
and opaque grafts. It is not exp(uV) for an invented uncoloured V.

The literal first two operator identities are

    J G D=(1/2)Q,
    J G^2 D=(1/4)(Q^2-Q).                            (3)

Here is a full-carrier verification of the second, rather than a diagonal
check. Two distinct successive merger events require either two disjoint
same-colour pairs or three roots of one colour. Each colouring event has
probability1/4, so every two-merger genealogy contributes one quarter of
its ordinary Q^2 weight.

For a given single merger at r current roots, the old/new total coloured
holding rates under that event have expectation

    1/2+3*(r-2)/4+binom(r-2,2)/2
          =(r^2-2r+2)/4.

Its signed coefficient is therefore -(r^2-2r+2)/4, exactly the Q^2-Q
coefficient divided by4. Finally the old coloured total rate has second
moment lambda_r^2/4+lambda_r/4: different pair indicators have product
mean1/4, including pairs sharing a root, and a repeated indicator has
mean1/2. This is the same diagonal of (Q^2-Q)/4. No other root-count
drop occurs in two generator factors. These arguments apply to every
labelled merger history and every prebuilt opaque input forest.

Consequently

    B(u)=I+(u/2)Q+(u^2/8)(Q^2-Q)+R_B,
    ||R_B||<=exp(Lu)*L^3*u^3/6.                     (4)

The OLD fair pair survival is(1+exp(-u))/2. Its matching ordinary exposure is

    tau(u)=-log((1+exp(-u))/2)
           =u/2-u^2/8+O(u^3).

On u>=0,0<=tau<=u/2, |tau''|<=1/4 and |tau'''|<=1. Thus

    |tau-u/2+u^2/8|<=u^3/6,
    |tau^2/2-u^2/8|<=u^3/16.

Comparing the ordinary exponential's Taylor formula with(4) gives,
for0<u<=1/(2L),

    ||B(u)-E_(tau(u))|| <= L^3*u^3.                 (5)

Indeed the sum of the two exponential remainders is at most
exp(Lu)*L^3*u^3/3, and the two coefficient errors contribute at most
L*u^3/6+L^2*u^3/16. For L>=2 and Lu<=1/2 their sum is below L^3*u^3.
This is a finite uniform analytic bound; no numerical experiment ran.

## 4. The actual reference and its logarithm

For h=-log t set

    tau=log(2-exp(-h)),        u=h+tau,
    v=2h-tau.

Then0<tau<=h, h<=u<=2h and h<=v<=2h. The actual reference is

    S(t)=E_h B(u) E_v,

and its exact pair exposure is

    h+tau(u)+v=3h,

because tau(u)=log(2-t)=tau for this u. Positive ordinary kernels have
norm1, so(5) yields

    ||S(t)-E_(3h)|| <=8*L^3*h^3                  (6)

whenever h<=1/(4L). This uses chronological multiplication, not a
commutation of ordinary populations past a nonordinary cell.

The same source lift and stochastic contraction give

    ||S(t)-I||<=L*(h+u+v)=4Lh,
    ||E_(3h)-I||<=3Lh.

For h<=1/(8L), both matrices lie within norm1/2 of I. The convergent
matrix-log series and a telescoping power difference prove

    ||log S(t)-log E_(3h)|| <=2||S(t)-E_(3h)||.

There is no commutative-log substitution here. The ordinary logarithm
is3hQ. Define the arithmetic matrix

    A_h=log S(t)/(3h).

Equations(6) give

    ||A_h-Q||<=6*L^3*h^2=:delta.                    (7)

For h<=h_M in(1), delta<=1/4. The logarithm is not a biological operation
and no negative population is inserted.

## 5. Projectors with an explicit perturbation constant

Both A_h and Q are count triangular with scalar blocks. Their respective
diagonals are

    a_r=log b_r(S(t))/(3h),        -lambda_r.

Each |a_r+lambda_r|<=delta. Distinct ordinary lambda values have gap>=1,
so |a_r-a_s|>=1/2 for r!=s. The scalar block gap also proves square-free
semisimplicity by the retained triangular resolvent argument.

Their spectral projectors are the literal finite polynomials

    P_r(A_h)=product_(j!=r)(A_h-a_j I)/(a_r-a_j),
    P_r(Q)=product_(j!=r)(Q+lambda_j I)/(lambda_j-lambda_r).

Every corresponding factor has norm at most3L+2. Subtracting one
corresponding pair and using the denominator gaps gives norm at most

    (6L+4)*delta.

For example, numerator difference is at most2delta, denominator difference
at most2delta, the ordinary numerator has norm at most L+Lambda=3L/2,
and the respective denominator lower bounds are1/2 and1. A telescoping
product subtraction therefore gives

    ||P_r(A_h)-P_r(Q)||
      <=(M-1)*(6L+4)*(3L+2)^(M-2)*delta.            (8)

These estimates use operator row norms, not the number of forest shapes.

## 6. The whole commutant estimate

Because K commutes with S(t), it commutes with A_h. The classical
same-carrier scalar-block centralizer identity gives

    K=sum_r k_r P_r(A_h).                          (9)

For completeness, a triangular eigenframe for A_h turns it into its
distinct scalar root-count blocks. K still has diagonal blocks k_r I.
Every off-diagonal block of a commuting matrix between two unequal
scalar eigenvalues is zero, proving(9). This does not determine the k_r.

Subtract the definition of K_0 in(2), apply(8),0<=k_r<=1 and(7), and sum
the M projector bounds. This gives exactly the C_M in(1) and proves(2).
The same projectors imply that K_0 commutes with Q, has diagonal blocks
k_r I and preserves row sums since k_1=1.

All source-length/coin/scale uniformity is now explicit. In particular,
nothing assumed that K was a prescribed fractional power of the reference.

## 7. Exact use in the active G3 route

For the active c=2^(-1/m), H=-log c and inferred index

    nu=log c/(4log t),       h=H/(4nu),

the theorem gives, once nu>=H/(4h_M),

    ||K-sum_r b_r(K)P_r(Q)|| <= C_M*H^2/(16*nu^2).  (10)

This is an ACTUAL all-length necessary estimate for every fitting main
word in the completed original-source reduction. It uses its real
unmarked private forest carrier; no original Code/register/same-count
update is silently identified with that carrier. The inherited protected
node/cohort/graft and all-core caller obligations remain as already proved.

The estimate is NOT

    dist(nu,Z)<=constant*nu^(-beta).

Unknown higher b_r(K) remain in(10). K_0 is not shown positive, ordinary,
a mixture, or physically factorizable. No implication from spectral
closeness to integer word phase is supplied. The new Jacobi/Beta
literature screen supplies none either: its mutation/carrier conditions
are different.

COMPLETED: the uniform quadratic matrix-projection part of this route.
STILL UNPROVED: AG-Pair's actual positive-word inferred-index estimate
and the original total G3 recognition/terminating-NO or impossibility
endpoint. No new full attack, additional master requirement, cap ladder
or source controller is selected. This lemma stays a component of the
existing single full-scope attempt.

Existing original IDs, parent complement gamma=1-g, one bank/tuple and
all owners/holds persist. No local Git mutation, subagent/chat, turn
wake/start/resume/interrupt, scientific/solver/model/native/compiler/
Lean/Cargo/Lake/CI action or held/USED/UNKNOWN replay occurred. Private
runtime remains RAM/encrypted before persistence with the existing identity.
