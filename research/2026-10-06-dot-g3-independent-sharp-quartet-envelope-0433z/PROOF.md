# A sharp-envelope INDEPENDENT invariant excluding positive kernels inside source closure

Contributor: dot / original G3 lane, 6 October 2026, 04:23 UTC.
Status: complete hand-proof candidate for independent review. The constructive RCF procedures are not executed. No numerical cutoff, selected numerical maximizer or Lean verification is claimed.

## 1. Exact source and inherited full-topology provider

Use the original fresh, unexposed, freely parameterized INDEPENDENT private bridge-word grammar at any finite cap m>=4. Every word has a strictly positive leading ordinary population, interior per-current-root routing probabilities, strictly positive arm durations and strictly positive ordinary connectors. The same physical parameter assignment supplies every capped forest row. Retain the original full labelled unranked forest kernel and ordinary ancestral-root completion.

For such a kernel K write

    a(K)=b_2(K), c(K)=b_4(K),
    T(K)=Pr(balanced rooted quartet after ancestral completion)-1/3.

The accepted quartet provider, proof SHA256 4ce42cd54c2467dba71a6a721ac892cbbdeb75b4e294544b2cf8427d8d56bfb5 and review af47782945ec9bc1b0408bcba5b2d8df3c46f807eec625e2dfadc78def11d78b, is immutable at
https://github.com/Sodelin/Research-Commons/blob/270793b319af174014f1b7de6e3849209c3476aa/research/2026-10-06-dot-g3-independent-quartet-topology-invariant-0403z/README.md .

Its exact premises used here are:

1. a and c multiply under chronological graft composition.
2. Every physical cell and word has c<=a^3. This uses the source no-merger formula and the classical Walkup/Liggett binomial-convolution theorem, with the finite-array transfer verified in that provider.
3. T(KL)=T(K)+c(K)T(L) whenever L is an actual suffix, also for an abstract stochastic graft K. The proof uses exchangeability of the three CURRENT opaque roots and preservation of previously formed subtrees.
4. T(E(z))=0. A positive trailing ordinary factor does not change T.
5. A bare cell B(p,x,y), with q=1-p, u=p(1-x), v=q(1-y), has exact polynomial quantities

       h(p,x,y)=1-a(B)=p^2(1-x)+q^2(1-y)=pu+qv,
       phi(p,x,y)=T(B)=(2/3)[q u^3+p v^3-3pq(u-v)^2],

   and phi<=144 h^3.

All these identities and inequalities extend to the closed cell cube [0,1]^3 by polynomial continuity. Closed parameters are used ONLY to define a compact envelope and source-closure witnesses, not as admitted finite source parameters.

## 2. A finite semialgebraic maximum, not an assumed whole-source description

For 0<=d<=1 define

    F(d)=max {phi(p,x,y): (p,x,y) in [0,1]^3, h(p,x,y)=d}.       (1)

Every level set is nonempty: p=0,y=1-d works. It is compact, so the maximum exists. Its graph is the following finite first-order real-closed-field formula:

    Max(d,t) iff 0<=d<=1 and
      exists p,x,y in [0,1]: h(p,x,y)=d and phi(p,x,y)=t,
      and forall p',x',y' in [0,1]:
          h(p',x',y')=d implies phi(p',x',y')<=t.

Therefore F is an effective semialgebraic function over Q. Only a SINGLE CELL with three bounded real variables is optimized. No semialgebraicity, finite parameterization or finite factor bound is assumed for the unbounded word image.

For 0<d<1/2 choose p=q=1/2 and x=y=1-2d. Then u=v=d and phi=(2/3)d^3. The inherited upper bound gives

    (2/3)d^3 <= F(d) <=144d^3.                                (2)

In particular F(d)>0 and F(0)=0.

## 3. A computably selectable monotonicity interval

Set G(d)=F(d)/d^2 on (0,1/2). This is positive semialgebraic, and (2) gives

    (2/3)d<=G(d)<=144d,

so G(d) tends to zero as d decreases to zero.

Use the classical one-variable semialgebraic monotonicity theorem: a definable real function admits a finite interval subdivision on which it is continuous and either constant or strictly monotone. A precise reference is Michel Coste, An Introduction to O-minimal Geometry, Theorem 2.1:
https://perso.univ-rennes1.fr/michel.coste/polyens/OMIN.pdf .
The primary theorem text was checked in the indexed copy of these lecture notes; the author PDF endpoint returned 403 during this retrieval. The result is classical, not a new source theorem. The theorem is being applied to the explicitly defined finite-cell value function G, not to an unproved definable set of arbitrary source words.

On the first interval adjoining zero, G cannot be a positive constant because its limit is zero. It cannot be strictly decreasing as d increases, because its value at a fixed positive d would then be bounded above by the limit zero from the left. Hence it is strictly increasing there. Choose a rational d_0 with 0<d_0<1/2 inside this interval, so G is strictly increasing on (0,d_0]. F(d)=d^2 G(d) is then strictly increasing and positive there as well.

This selection is effective without a precomputed explicit envelope formula. Enumerate positive dyadic candidates d_0<1/2 and use exact RCF decision to test

    for all 0<u<v<=d_0, Max(u,U) and Max(v,V)
        imply u^2 V>v^2 U.

The displayed maximum relations are finite RCF formulas, and the theorem guarantees that some candidate passes. This is a terminating mathematical algorithm; it has not been run here. An endpoint can always be chosen strictly inside the monotonicity interval, so no unverified behavior at its far endpoint is used.

## 4. The envelope bounds every padded physical append

Let L=B E(z) be a strict physical append. Its total pair loss is e=1-a(L), while the bare loss is h=1-a(B)<=e. If 0<e<=d_0, then

    T(L)=T(B)<=F(h)<=F(e),                                  (3)

using the exact trailing-gap identity and monotonicity of F. A pure ordinary append has T=0<F(e). Thus the one-cell envelope applies to the actual append grammar, including its mandatory positive connector; no hypothetical zero gap is inserted into a finite source.

## 5. A strict semialgebraic inductive invariant for all word lengths

Within the capped stochastic graft algebra impose a in (0,1), 0<=c<=a^3, and

    either 1-a>d_0,
    or T(K)<F(1-a).                                        (4)

Formula (4) is semialgebraic over the selected rational d_0, by using Max to express its comparison. The large-loss branch is absorbing because pair survival cannot increase under an actual append.

Initialization at E(z), 0<z<1, satisfies c=z^6<=z^3=a^3 and either the escape condition or T=0<F(1-a).

Now take ANY abstract stochastic graft state K satisfying (4), and append an actual L. Suppose the output does not escape. Write

    d=1-a(K)>0, e=1-a(L)>0, a=1-d,
    w=1-a(KL)=d+a e<=d_0.

Both d and e are at most w. The old state cannot have escaped, so T(K)<F(d). By (3), the cocycle and c(K)<=a^3,

    T(KL)=T(K)+c(K)T(L)
          <F(d)+a^3 F(e).

Positivity of F(e) justifies replacing c(K) by a^3 after first replacing T(L) by F(e), even if T(L) is negative. Monotonicity of G gives

    F(d)+a^3 F(e)
      <=F(w)[d^2+a^3 e^2]/w^2 <F(w),                       (5)

because

    w^2-d^2-a^3 e^2=2d a e+a^2 d e^2>0.

The diagonal condition is preserved by c(KL)=c(K)c(L)<=a(K)^3 a(L)^3. Stochasticity and the source-compatible graft constraints are preserved by actual composition. This proves induction on every abstract state of the predicate, without assuming it already has a source history. In particular every strict finite source satisfies

    T(K)<F(1-b_2(K)) whenever 0<1-b_2(K)<=d_0.               (6)

The strict positive leading ordinary edge is an essential source premise: it initializes a STRICT inequality. The proof excludes all alternative strict words, not merely a selected one-cell parameterization.

## 6. Positive, nonsingular closure points excluded by the invariant

Fix any rational d in (0,d_0), and choose a closed-cell maximizer (p_*,x_*,y_*) in (1). Since the data and the maximum relation are over Q(d), RCF algebraic sampling supplies an algebraic maximizing triple and algebraic F(d). Let

    K_*=B_I(p_*,x_*,y_*).

Then b_2(K_*)=1-d, T(K_*)=F(d)>0. The strict invariant (6) proves that NO finite positive INDEPENDENT word has this full capped kernel.

It is nevertheless in the actual source closure. Approximate any closed arm/coin parameters by strict ones and append strictly positive leading/trailing ordinary gaps whose survivals tend to one. The resulting original source words converge to K_* in every fixed cap by polynomial continuity, using one coherent parameter sequence across arities.

This is not a zero-coordinate or singular-kernel exclusion. Positivity of phi implies p_* is strictly between zero and one: at p=0 or1, phi=0. It also forces both arm LOSSES to be positive. If u=0, the formula gives

    phi=(2/3)p v^2(v-3q)<=0,

because v<=q; the v=0 case is symmetric. Thus x_*,y_*<1. They cannot both be zero, because then d=p_*^2+(1-p_*)^2>=1/2, contrary to d<d_0<1/2. Hence at least one arm has survival strictly between zero and one, and its routing probability is strictly positive.

For any finite entering-root count, there is positive probability that ALL roots route to that finite positive arm. Ordinary Kingman evolution for its strictly positive finite duration assigns positive probability to every allowed labelled binary forest graft outcome: choose any compatible finite merger order and times, followed by no further merger before the arm ends. The unchanged forest also has positive probability. Therefore K_* has strictly positive entries on every structurally allowed forest transition at every finite cap, and strictly positive no-merger diagonal characters. It is a unit in each finite capped forest algebra.

The SAME algebraic closed cell provides a coherent all-arity family. Its cap-four restriction already rules out a strict INDEPENDENT realizing word at every larger cap. No finite-cap extrapolation is used to establish the source formulas.

## 7. Constructive exact status and whole-fibre use

The following finite procedure is proved to terminate:

1. Form the rational polynomial Max formula from section 2.
2. Find a rational d_0 by the RCF monotonicity search in section 3.
3. Choose, for example, rational d=d_0/2.
4. Use RCF algebraic sampling on Max(d,t) and its maximizer equations to return t and an algebraic maximizing triple.
5. Compile its full capped kernel by the inherited polynomial source map.

The result is an exact algebraic positive-kernel NO certificate inside actual source closure, with proof of nonattainment by (6). This procedure, its threshold and a particular output kernel have NOT been executed or numerically evaluated. No runtime bound or practical QE claim is made.

The entire symbolic inequality (4) is also one finite effective semialgebraic invariant, uniformly over the continuum of small-loss states. In an original coupled core it may constrain the SAME shared full symbolic INDEPENDENT kernel. A core-wide rejection is sound if RCF shows that its complete target fibre lies outside this invariant; all static parameters, row sharing, ties and observation coarsenings must remain in that exact compiler test.

We do not assert that the maximizer family has been encoded as one full negative original input across every alternative core. Exposed or paired registers and additional source ties are outside the immediate fresh-slot theorem. Completeness for arbitrary nonattained fibres remains the original G3 obligation. Ordinary-target G4 stopping and exact-return questions remain open.

## 8. What this adds to the accepted quartet bound

The coarse cubic bound detected points outside source closure. The sharp finite-cell envelope now gives a NONCLOSED inductive separator at genuine positive, nonsingular points inside the INDEPENDENT closure, and a terminating exact algebraic construction of such points. This follows from the source-specific chronological cocycle, the actual one-cell optimization and classical semialgebraic monotonicity. It does not assume arbitrary word images are semialgebraic or that convex positive realizations have physical word factorizations.

The coalescent/ULC/cocycle source work is explicitly inherited from the accepted quartet proof. Compact polynomial optimization, RCF, algebraic sampling and one-variable semialgebraic monotonicity are established methods. Historical novelty is unverified. No new computation or formal-kernel verification is claimed.
