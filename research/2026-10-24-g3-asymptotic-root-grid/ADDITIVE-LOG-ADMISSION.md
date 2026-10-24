# Weak-cell admission for additive joint diagonal log guards

Stable key: G3-JOINT-DIAGONAL-LOG-ADMISSION-01.

24 October2026UTC. Existing G3 owner.
**PROVED BY HAND as a corollary of the completed paired-diagonal rank
supplier.** Author self-review complete; independent correctness review
and Lean formalization have not been performed. No source/coefficient/
symbolic/numerical control, solver/QE, model/native/compiler/build job ran.

This records a reuse consequence and closes one proposed guard use-site.
It is NOT a new full attack, AG-Pair, a physical factorization, or original
G3 recognition/impossibility. No historical priority or new source theorem
is claimed.

## 1. Exact private source and guard class

Fix ANY finite M>=3. Let lambda_n=binom(n,2),2<=n<=M, and
Lambda=lambda_M. A literal strict equal-arm independent cell is

    B(e^(-h),e^(-h),g),       h>0, 0<g<1.

It routes each entering CURRENT root independently. Its original parent0
probability is g; native parent1 gamma=1-g. Previously built subtrees are
opaque. Its natural unexposed COMMON kernel on the SAME tuple is E_h.
No exposed bit is averaged again or granted as an extra observation.

Write its actual I no-merger probability as b_n(h,g), and put

    v_n(h,g)=log b_n(h,g)+lambda_n*h,
    v(h,g)=(v_2,...,v_M),     lambda=(lambda_2,...,lambda_M).

Ordinary populations contribute zero to these normalized coordinates.
On an actual finite equal-arm word W,

    V_n(W)=log b_n^I(W)-lambda_n*log b_2^C(W)
          =sum_cells v_n(h_i,g_i).                 (1)

This is exact multiplicativity of no-merger diagonals on one source.
It is not additivity of the full matrix logarithm.

An admitted guard in THIS class is a fixed real coefficient vector alpha
such that

    alpha.v(h,g)>=0 for EVERY h>0 and0<g<1.         (2)

Alpha may depend on a target/reference, but is fixed over all cells in
that source. Validity is global on the equal-arm alphabet. A globally
nonnegative ordinary-neutral additive linear combination of finitely many
I/COMMON diagonal logs reduces to this form on the equal-arm COMMON face:
COMMON logs equal lambda_n*log b_2^C, and the ordinary term cancels.

Prefix-dependent coefficients, nonlinear guards, validity restricted to a
proper target fibre, and a budget-conditioned affine offset are outside(2).

**Corollary.** There exists h_0(M)>0 such that EVERY nonzero alpha satisfying
(2) is STRICTLY positive on EVERY strict cell with0<h<=h_0(M), uniformly
over its coin g. The threshold is independent of alpha and g.

Consequently no such guard can be tight on sufficiently weak reference
cells or on any word containing one of them. Other cells have nonnegative
scores, and ordinary populations contribute zero. This includes the
intended large integer powers of the current reference S(t).

## 2. Exact reused suppliers and scope comparison

The controlling completed source is
[G3-WEAK-EQUAL-ARM-PAIRED-DIAGONALS-01](https://github.com/Sodelin/Research-Commons/blob/d315068224c12dc741798107bb4b558ec66f2888/research/2026-10-24-g3-weak-equal-arm-paired-diagonals/PROOF.md),
16564B/SHA256
6e22486e0cd41ec18b1fe869418a1ceccc681822534f78f0393f526bf3d3cd67.
Its statement and actual-source rank/limits in Sections7--8 were read.
For every0<C<D<sqrt(C)<1 it supplies a strict equal-arm word with COMMON
E(C), I diagonals D^lambda_n through M, and rank M for the joint scalar
map. The OLD8October interior-coin coefficient, regular unweighted-sum
lemma, IFT and forward original-source insertion remain attributed to
their completed providers. None is derived or executed again here.

The COMPLETE controlling COMMON-only predecessor was also read:
[GLOBAL-LOG-GUARD-REUSE.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-13-dot-g3-log-guard-reuse-0633z/GLOBAL-LOG-GUARD-REUSE.md),
9407B/SHA256
51490003ba0a4359e217fa40f01c797d9568a5f806ef4b75bec0220498e401b3,
blob54214ee159e1b6782d2e5b8dade3236ea54dc571.
Its exact cone/strict-no-zero theorem is PROVED with its retained scoped
review. It explicitly does not supply an automatic I/BOTH conclusion.
The present joint normalized I alphabet and sufficiently-weak conclusion
are different. No new COMMON cone or all-strength joint classification
is claimed.

The COMPLETE OLD single-fair-cell proof, its complete scoped HAND ACCEPT
and package README were read at8b96f4fb:
research/2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z/g4-paired/
PAIRED-NONLINEAR-SINGLE-FAIR-CELL-FORCING.md,
9469B/SHA2562b73ef2baf4a573667c006e7e128ad5779b7f652ae5978b3d08bfe7cacbff9f8,
blob88af75747882a62c3ec8fdd18e3604be156f9a7d;
INDEPENDENT-CONSTRUCTION-REVIEW.md,
6908B/SHA256a73156ae039dad6a583d5572a2def6eb702aebf1a1a9277ed3e5e5346a74f5b8,
blobee22d29a8962ec90d9b7ce973f639b8131520bdc.
Its normalized nonlinear guard s>=3r^2-3r+1 has equality exactly for
ONE fair cell. It is strict on every multi-cell word and is not the
unknown-index detector. That completed theorem is reused, not reopened.
The accompanying README2752B/SHA64c820c0... supersedes its frozen
candidate/pending heading.

The local current AND archived joint-log/paired-log/strict-zero aliases
were checked before this corollary. This is a bounded prior comparison,
not an absence/novelty theorem. The argument below uses completed rank,
classical local openness and a bounded Bernoulli-cut estimate.

## 3. The ordinary direction is an interior point of the actual log cone

Define the finite conic hull

    C_log={sum_(j=1)^L a_j*v(h_j,g_j):
           L finite, a_j>=0, h_j>0,0<g_j<1}.          (3)

This is mathematical dual geometry. Real weights a_j are NOT physical
fractional cells. No closure or physical membership assertion is made.

Apply the completed paired source/rank supplier at C=1/4,D=1/3. Its
actual word has

    V=(log(4/3))*lambda.

The joint COMMON/I diagonal map has rank M. Transforming its outputs
invertibly to(H_COMMON,V_2,...,V_M) preserves rank, so the V map has rank
M-1 at that SAME positive word. In particular its image contains an open
neighborhood of V. Each image point is a sum of actual cell log vectors
by(1), so this whole neighborhood belongs to C_log.

Scaling by1/log(4/3)>0 proves that lambda is an INTERIOR point of C_log.
There is therefore some rho_M>0 for which the CLOSED max-norm ball

    {lambda+w: ||w||_infinity<=rho_M}

is contained in C_log. Choose a smaller radius if needed. This conclusion
uses a finite actual word/rank supplier; it is not an external mixture
declared realizable, nor an unexecuted numerical rank assertion.

If alpha satisfies(2), it is nonnegative on C_log. Evaluating it on
lambda-rho_M*sign(alpha), component by component, yields

    alpha.lambda >=rho_M*||alpha||_1.               (4)

Thus every nonzero valid dual has a strict, uniform-angle separation
from this ordinary direction. This is the needed consequence of the
already supplied full scalar rank.

## 4. Uniform weak-cell estimate, including arbitrarily rare coins

Set p=g(1-g)>0. For n entering current roots let K_n be Binomial(n,g).
The literal equal-arm source formula gives

    b_n=e^(-lambda_n*h)*E exp(h*X_n),
    X_n=K_n*(n-K_n),
    v_n=log E exp(h*X_n).                           (5)

Indeed lambda_n-lambda_k-lambda_(n-k)=k(n-k). All routes and no-merger
holdings in(5) belong to the original cell. There is no per-leaf routing
inside an old subtree.

We have0<=X_n<=lambda_n and E X_n=2p*lambda_n. Jensen and log z<=z-1,
followed by the elementary exponential remainder bound, give

    0<=v_n-h*E X_n
       <=E[exp(hX_n)-1-hX_n]
       <=(h^2/2)*exp(lambda_n*h)*E X_n^2
       <=p*lambda_n^2*exp(lambda_n*h)*h^2.

Consequently

    ||v(h,g)/(2p*h)-lambda||_infinity
       <=(Lambda^2/2)*exp(Lambda*h)*h.              (6)

Crucially p cancels from this relative estimate. It is uniform over ALL
strict coins, even along g->0 or1. It gives no coin-independent positive
probability margin: p remains positive but can be arbitrarily small.

Choose

    h_0(M)=min(1/Lambda, rho_M/(exp(1)*Lambda^2)).    (7)

For0<h<=h_0, the right side of(6) is at most rho_M/2. Combining(4),(6)
proves the quantitative strictness

    alpha.v(h,g)
       >=p*h*rho_M*||alpha||_1>0                  (8)

for every nonzero valid alpha. This proves the corollary.

Existence of rho_M is supplied by completed actual rank/local openness.
No numerical interior radius, source tuple, positivity optimization or
guard-validity solver was computed. Formula(7) specifies the remaining
bound once any such interior radius is chosen; no new effective G3
certificate-acquisition procedure is claimed.

## 5. Admission for the current reference

Reuse the actual paired reference

    S(t)=E(t) B_I(t/(2-t),t/(2-t),1/2) E(t^2*(2-t)).

For0<t<1 its bigon exposure is

    h_B=-log(t/(2-t))
       =-log t+log(2-t)<=2*(-log t).

Thus for any fixed finite M, sufficiently large intended integer powers
S(c^(1/(4N)))^N contain only cells covered by(8), at the same fixed
COMMON c. Their normalized diagonal log score is N times the STRICT
positive bare score; ordinary pads cancel.

Hence a nonzero globally nonnegative ordinary-neutral additive JOINT
diagonal log character cannot be tight on those witnesses, even when
its coefficients depend on t or the target. The threshold in(7) is
independent of that coefficient vector. This rules out this particular
alphabet-enforcement/phase-guard shortcut.

It does NOT refute AG-Pair. The active full commutator uses chronological
off-diagonal forest equations, and those are outside the diagonal score
class. Nor does it exclude nonlinear or transported source-dependent
guards, validity only on a proper fibre, or actual positive factorization.

## 6. Original endpoint and evidence limits

This is a HAND reuse corollary and source-admission correction. It is
not another all-order source coefficient theorem, mathematical discovery
count, new controller or full replacement strategy. The already completed
one-fair-cell guard, paired-diagonal synthesis, COMMON log cone, all-core
caller, arithmetic reduction and two matrix/source bounds remain closed.

AG-Pair's all-length near-integer implication and original total G3
recognition/terminating-NO or impossibility remain UNPROVED. No source
count bound or new acceptance requirement is inferred.

All original IDs, parent complement, one physical tuple, private current-
root routing, SAME natural bank, protected menus and opaque grafts keep
their existing scope. No local Git, subagent/new chat, peer wake/start/
resume/interrupt, scientific/source/solver/QE/model/native/compiler/Lean/
Cargo/Lake/CI action, writer bypass or held/USED/UNKNOWN replay occurred.
Private runtime stays RAM/encrypted before persistence with the ONE identity.
