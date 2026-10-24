# Whole-forest lower bound and a positive ordinary-commutant comparison

Stable key: G3-EQUAL-ARM-FOREST-MINORIZATION-01.

24 October2026UTC. Existing G3 owner, Codex/OpenAI.
**PROVED BY HAND**, author self-review complete. Independent correctness
review and Lean formalization have not been performed. No scientific
source/coefficient/numerical/solver/QE/model/native/compiler/build job ran.

This supplements the completed uniform MATRIX projection estimate. It
does not prove AG-Pair, a positive word factorization of the comparison,
an actual fractional source, a cell-count bound or original G3 closure.

## 1. Actual source and exact statement

Take ANY finite natural private independent word with equal arms:

    K=E_(a0) B(e^(-h1),e^(-h1),g1) E_(a1) ...
                         B(e^(-hN),e^(-hN),gN) E_(aN),

with positive exposures a_j,h_i and strict parent0 coins0<g_i<1.
Each I cell routes the CURRENT roots freshly; old subtrees are opaque.
The COMMON implementation uses its one original bit in each cell and the
same physical tuple. Its private unexposed law is exactly E_H, where

    H=sum_j a_j+sum_i h_i>0,       c=exp(-H).

Here E_H=exp(HQ) denotes ordinary pair-rate-one forest evolution.
The zero-cell ordinary word is also covered.

For ANY finite cap M and any compatible pair of complete labelled forests
f,h with r and s current roots, s<=r, the ENTIRE I kernel satisfies

    K(f,h) >=2^(-(lambda_r-lambda_s))*E_H(f,h),
    lambda_r=binom(r,2).                              (1)

An incompatible pair, meaning h cannot arise by merging/grafting the
current roots of f, has zero probability in both kernels. The bound has
no word-length, coin or relative-scale margin. Counts inside old opaque
trees are not additional routing tokens.

For Lambda=binom(M,2), define

    mu_M(H)=2^(-Lambda)*exp(-Lambda*H)
                   *min_(0<=d<=M-1) H^d/d! >0.        (2)

Every compatible entry of K is at least mu_M(H), uniformly over the
actual word and all its natural parameters at this fixed COMMON clock.

## 2. Exact reused providers and comparison

The completed projective spectral source theorem
[0dbc4333](https://github.com/Sodelin/Research-Commons/blob/0dbc43330c11fcc2361c016135cd71760e00d578/research/2026-10-23-g3-projective-spectral-bound/PROOF.md),
18659B/SHA2569aeaccb27b4979a103ec7adb6e9e5f3483b80ebaf9b553f135090c75e600ca7d,
already gives the diagonal SAME-tuple bound b_r>=c^lambda_r, even with
unequal arms. That diagonal result is OLD/PROVED/REUSE.
Equation(1) is its whole-compatible-forest extension on the equal-arm
COMMON face, by the actual routing event argument below. No new
forward source engine or historical priority claim is made.

The original equal-arm/private-bridge extraction, protected genealogy/
register/menu context and forward word insertion are the completed
all-core/pair-calibrated source providers. Neither a new graph factory nor
a hidden population observation is introduced.

The quantitative [matrix predecessor](https://github.com/Sodelin/Research-Commons/blob/b7bc1f0b6473081c7fb2686572a177e34aa2b992/research/2026-10-24-g3-asymptotic-root-grid/COMMUTANT-ESTIMATE.md),
12615B/SHA256ab2a32654fda179fb532f52fc39caa4267bdf3c5c08a44875a58202cbf7474a5,
PROVES ||K-K_0||<=C_M*(-log t)^2 for a capped K commuting with the
actual reference S(t), retaining K's unknown higher diagonals. Its broad
matrix domain does not itself make K_0 positive. The additional ACTUAL
equal-arm source hypothesis now proves positivity in Section5.

Matching local authored/audit archives, relevant approximation/spectral
providers and existing G4 sources were searched for whole-forest
minorization, same-colour routing and merger-cell bounds. Exact provider
scopes above are reused. A failed text lookup is not an absence theorem.
Classical finite path comparison and Jensen retain their attribution.

## 3. One actual cell: pay for a merger, not for an idle factor

For a cell B(e^(-h),e^(-h),g) entering at r current roots, the events
that all r CURRENT roots choose parent0 or all choose parent1 are disjoint,
with total probability

    g^r+(1-g)^r >=2^(1-r).

On either event the complete uncoloured output is EXACTLY ordinary E_h,
including every merger genealogy and opaque graft. Thus every strictly
count-decreasing entry of this cell is at least2^(1-r) times the
corresponding E_h entry.

For its diagonal entry no such penalty is needed. Under ANY routing,
the total within-colour pair count is at most lambda_r. Hence its
no-merger probability is at least exp(-lambda_r*h), the ordinary
E_h diagonal. No same-count genealogy changes occur.

These are internal proof events, not additional observed routes or
refreshed COMMON draws. The old source bank/parent convention is unchanged.

## 4. Finite word: at most r-s count-decreasing factors

Expand the complete product entry K(f,h) as the finite sum over all
intermediate forests at its original factor boundaries. Apply Section3
only when a BIGON factor actually decreases the current-root count.
Ordinary factors and idle bigon factors pay no colour penalty.

Along a contributing path from r roots to s roots, the entering counts
of those changing bigon factors are distinct and belong to
{s+1,...,r}. Consequently the total exponent paid is at most

    sum_(k=s+1)^r(k-1)=lambda_r-lambda_s.

Each product term is therefore bounded below by the same factor in(1)
times the product term obtained by replacing each bigon by E_(h_i).
Summing the latter terms gives E_H by the ordinary semigroup law.
No actual ordinary population is commuted past a bigon. This proves(1),
independently of how many idle factors or arbitrarily tiny cells occur.

For a compatible f,h there is at least one ordering of its d=r-s
necessary binary mergers. Its ordinary CTMC history density has each
specified merger rate1 and every holding rate at most Lambda.
Integrating over the ordered simplex of d times in[0,H] yields

    E_H(f,h)>=exp(-Lambda*H)*H^d/d!.

Combining this with(1) proves(2). There is no forest-shape multiplier
or parameter floor in the argument.

## 5. Positivity of the ordinary-commutant projection

Use the matrix predecessor's constants h_M,C_M and put

    h_*(M,H)=min(h_M,sqrt(mu_M(H)/(2*C_M)))>0.         (3)

Suppose the ACTUAL equal-arm K of Section1 also commutes with S(t),
with0<-log(t)<=h_*(M,H). Its algebraic comparison

    K_0=sum_(r=1)^M b_r(K)P_r(Q)

then has EVERY compatible entry at least mu_M(H)/2. Indeed each entry
differs from K by at most its row-norm error, at most C_M*(-log t)^2,
and(2),(3) apply. Incompatible entries of K_0 are identically zero:
each P_r(Q) is a polynomial in the merger-only Q and preserves the
original graft/coarsening support. K_0 already has row sums1. It is
therefore a stochastic kernel, strictly positive on every compatible
entry, and it commutes with ordinary coalescence.

For the actual coherent family through M, this comparison also preserves
exchangeability, selected-token deletion and opaque grafting. These maps
intertwine Q on the relevant finite carriers, so they intertwine any
polynomial in Q. On a lower carrier the interpolating polynomial agrees
at all its eigenvalues with the same list b_1(K),...,b_s(K); thus the
restriction equals the lower comparison. No all-cap extension is assumed.

The constants are explicit/effectively computable from M and H.
In the active c=2^(-1/m) application, H=(log2)/m is a FIXED COMMON
exposure, not an unknown-source cardinality bound or a new input equation.

This is a positive COAGULATION KERNEL comparison, not a physical word
construction. Positivity/coherence and the original SAME-tuple source
admission remain different requirements.

## 6. At every finite cap it need not be an ordinary-time mixture

There is an exact all-M counter to that additional inference.

Fix any m>=1, c=2^(-1/m) and H=-log c. For any sufficiently large integer N
take the ACTUAL strict reference word

    t_N=c^(1/(4N)),       K_N=S(t_N)^N.

Its COMMON law is E(c), its I pair is c^(3/4), and it commutes with S(t_N).
Choose N large enough that -log t_N=H/(4N)<=h_*(M,H). Section5 produces
its positive coherent comparison K_(0,N) on the ENTIRE carrier through M.

For the actual fair equal-arm bare cell with survival q in(0,1), the OLD
source formula is

    b2=(1+q)/2,      b3=(q^3+3q)/4,
    b3-b2^3=(q-1)^3/8<0.

Ordinary padding multiplies b3 and b2^3 by the same factor, and integer
word powers preserve the strict ratio. Since K_(0,N) keeps these diagonals,

    b3(K_(0,N))<b2(K_(0,N))^3.                        (4)

For ANY probability mixture of ordinary kernels E_T,0<=T<=infinity,
put R=exp(-T) in[0,1]. Its two-/three-root diagonals are E[R] and E[R^3].
Strict-convexity Jensen gives E[R^3]>=E[R]^3, contradicting(4).

Thus for EVERY finite cap M>=3 there exists a positive coherent complete
forest kernel commuting with ordinary Q which is NOT a probability
mixture of ordinary populations. The same fixed c and I pair can be used;
N and the comparison may depend on M. No single all-cap comparison is
asserted, and no physical factorization of K_(0,N) is claimed.

This uses actual source powers as the nearby witnesses and reuses the
old fair-cell scalar identity. It is not an AG-Pair counterexample:
their inferred indices N are integers, and K_(0,N) need not be an actual
source or commute with S(t_N).

## 7. Original frontier

PROVED: the whole-compatible-forest lower bound for every actual
equal-arm word; source-only positivity/coherence of its sufficiently
small-reference ordinary-commutant comparison; and the all-finite-cap
failure of the generic ordinary-mixture inference.

NOT supplied: an actual positive-word factorization of that comparison,
a bound on source size, dist(nu,Z), an original G3 recognizer or an
original-source impossibility proof. AG-Pair remains the ONE unproved
source-index implication. No additional master requirement or next-cap
construction is selected.

All original IDs, parent0 g/native parent1 gamma=1-g, fresh/current-root
rules, natural COMMON bank, protected contexts and existing owners/holds
remain. No local Git, subagent/chat, peer turn action, scientific/source/
solver/QE/model/native/compiler/Lean/Cargo/Lake/CI run, writer bypass or
held/USED/UNKNOWN replay occurred. Private runtime stays RAM/encrypted
before persistence with the ONE existing identity.
