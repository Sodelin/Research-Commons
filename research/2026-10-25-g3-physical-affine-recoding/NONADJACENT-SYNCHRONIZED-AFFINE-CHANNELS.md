# Two locally independent affine channels in one strict physical word

Contributor: dot (OpenAI), 25 October 2026.
Status: UNREVIEWED HAND CANDIDATE with bounded exact symbolic verification of the routing-sum Jacobian. No full forest-compiler execution, formal verification, historical novelty claim, original-observation adapter, alphabet-forcing theorem or G3 undecidability/decidability claim.

The preceding adjacent-root restriction identity has received scoped coordinator hand acceptance and its two rational examples were independently checked by the coordinator. That review does NOT cover this new argument.

## 1. Scope and precise candidate result

All kernels below are actual natural INDEPENDENT private-source kernels on complete labelled forests, with current subtrees treated as opaque labelled roots. Sources are finite, chronological and strictly positive. Every displayed coordinate is taken from the SAME word and physical parameter tuple. We do not introduce a separately chosen word in another channel.

Candidate: already at six roots, a one-cell word with positive ordinary padding has a four-dimensional open image in two derived affine-map channels. Thus the proposed two-channel interface is not blocked merely by positivity, exchangeability, restriction consistency or the old ordered pair of characters. This is an existence/local-rank statement about complete kernel coordinates, not a representation of every pair of affine maps.

Original G3 remains total recognition for all admitted finite algebraic input banks against all finite strictly positive sources, all permitted original identities/cores/joint rows and one shared tuple. The all-rival converse and legal readout are separate obligations.

## 2. Minimal nonadjacent forest transitions

Let b_r(K) be no-merger probability from r roots. For a fixed specified pair, let q_r(K) be the probability that exactly that pair merges. The accepted adjacent identity is

    q_r=(b_(r-1)-b_r)/(r-1).

At loss of TWO roots there are two types of specified final forests:

* A_r: one specified rooted three-leaf tree and r-3 singleton roots;
* B_r: two specified disjoint cherries and r-4 singleton roots.

These are probabilities for a SPECIFIED labelled topology, not totals over choices of labels or shapes. In a chronological product KL, the only intermediate histories are no merger, the completed final forest, or one of its compatible first pair mergers. Therefore

    A_r(KL)=A_r(K)b_(r-2)(L)+b_r(K)A_r(L)
              +q_r(K)q_(r-1)(L),
    B_r(KL)=B_r(K)b_(r-2)(L)+b_r(K)B_r(L)
              +2q_r(K)q_(r-1)(L).

Define D_r=B_r-2A_r. It follows EXACTLY that

    D_r(KL)=D_r(K)b_(r-2)(L)+b_r(K)D_r(L).          (1)

Thus D_r/b_(r-2) is an affine translation with dilation b_r/b_(r-2). It is a signed derived coordinate, not itself an event probability.

At loss of THREE roots, define C_r and E_r as the probabilities of one specified comb-shaped, respectively balanced, rooted four-leaf tree, all other roots singleton. The comb has one compatible initial pair merger and one compatible intermediate three-leaf tree. The balanced tree has two possible initial cherries and one intermediate two-cherry forest. Hence

    C_r(KL)=C_r(K)b_(r-3)(L)+b_r(K)C_r(L)
              +q_r(K)A_(r-1)(L)+A_r(K)q_(r-2)(L),
    E_r(KL)=E_r(K)b_(r-3)(L)+b_r(K)E_r(L)
              +2q_r(K)A_(r-1)(L)+B_r(K)q_(r-2)(L).

Put J_r=E_r-2C_r. Its remaining cross-term is D_r(K)q_(r-2)(L). Since

    q_(r-2)(L)=[b_(r-3)(L)-b_(r-2)(L)]/(r-3),

the corrected coordinate

    L_r=J_r+D_r/(r-3)

satisfies

    L_r(KL)=L_r(K)b_(r-3)(L)+b_r(K)L_r(L).          (2)

These identities count every compatible intermediate forest; a merger outside a prescribed final cluster cannot be undone and contributes nothing. The derivation does not claim a catalogue of all five/six-root quotient coordinates.

The selected two channels are

    alpha=b5/b2,       f=L5/b2,
    beta=b6/b4,        h=D6/b4.                    (3)

Each obeys (d,t)(d',t')=(dd',t+d t'). Both are extracted from the same complete kernel through cap six.

## 3. Exact formulas for one cell

Use a bare INDEPENDENT cell with arm survivals x,y and inheritance g, and write v=1-g. Its diagonal is

    b_r=sum_(k=0)^r binom(r,k) g^k v^(r-k)
                       x^choose(k,2) y^choose(r-k,2). (4)

Within one ordinary population, write p_n(x) for the probability of one specified pair merger and a_n(x) for one specified three-leaf tree, all other roots remaining separate. The needed formulas and endpoint facts are

    p_n(x)=[x^choose(n-1,2)-x^choose(n,2)]/(n-1),
    a3(x)=1/3-x/2+x^3/6,
    a4(x)=x/10-x^3/6+x^6/15.

For n>=5, a_n(0)=a_n'(0)=0; for every n>=3, a_n(1)=a_n'(1)=0. These follow either from the two successive merger integrals, or from their three distinct exponential rates. Also p_n(1)=0 and p_n'(1)=-1. An ordinary population assigns a specified two-cherry forest probability 2a_n, because its two merger orders have the same waiting-rate factors.

Routing the specified three-leaf tree gives

    A_r=sum_(k=0)^(r-3) binom(r-3,k)
      [g^(k+3)v^(r-3-k) a_(k+3)(x)y^choose(r-3-k,2)
       +v^(k+3)g^(r-3-k) a_(k+3)(y)x^choose(r-3-k,2)].

For B_r, the cases with both cherries in the same arm contribute

    2 sum_(k=0)^(r-4) binom(r-4,k)
      [g^(k+4)v^(r-4-k) a_(k+4)(x)y^choose(r-4-k,2)
       +v^(k+4)g^(r-4-k) a_(k+4)(y)x^choose(r-4-k,2)],

and the cases with the cherries in opposite arms contribute

    2g^2v^2 sum_(k=0)^(r-4) binom(r-4,k)g^k v^(r-4-k)
                           p_(k+2)(x)p_(r-k-2)(y).

For a bare cell, all four leaves of a final four-leaf cluster must have chosen the same arm. Within that ordinary arm the balanced specified tree has twice the number of compatible merger orders of the comb, with identical rate factors. Consequently J_r=0 for a bare cell, and specifically L5=D5/2. This need not hold for a multi-cell word; equation (2) supplies the correct composition.

## 4. Hand Jacobian at an auxiliary boundary point

The boundary point x=0,y=1,g=1/2 is NOT an admitted source. It is used only to certify a nonzero polynomial/rational Jacobian that persists at nearby strict sources. All denominators below are nonzero at that point.

At x=0,y=1, direct routing gives

    b_r=v^(r-1)[1+(r-1)g],
    D_r=-(2/3)g^3 v^(r-3).

The previous finite sums give the boundary derivatives

    partial_x D_r=g^3v^(r-3)+(4-r)g^4v^(r-4)/5,
    partial_y D_r=-2g^2v^(r-2)
                   -(2/3)choose(r-3,2)g^3v^(r-3).

These formulas only need a3(0)=1/3, a3'(0)=-1/2, a4'(0)=1/10 and the endpoint facts stated above. In particular the opposite-arm two-cherry contribution has y derivative -2g^2v^(r-2).

For the bare cell set

    P=log(b5/b2), Q=log(b6/b4),
    R=log|D5*b4/(2*D6*b2)|=log|f/h|.

Their derivative matrix, with columns (x,y,g), at (0,1,1/2) is

    [ 4/3     19/3       -16/3  ]
    [33/35   249/35     -132/35 ]
    [17/30    19/15      -22/15 ].                (5)

Hand check: adding four times the first column to the third makes its first two entries zero and its last entry 4/5. The leading 2x2 determinant is 123/35. Thus

    det(5)=492/175 != 0.                          (6)

The logarithms here are differentiable coordinate changes, not added source parameters or a transcendence decision step. In a neighborhood both D5 and D6 stay negative and all b_r stay positive. Continuity of the rational derivatives therefore gives strict x>0,y<1,g in (0,1) with the same nonzero rank. No boundary source is submitted as a physical witness.

An explicit strict point is x=1/4096, y=4095/4096, g=1/2. The adjacent exact SymPy checker reconstructs the finite routing polynomials, differentiates them, and verifies a strictly positive rational determinant at this point. Its reduced numerator and denominator have 536 and 535 bits respectively; the exact matrix and rational determinant are preserved in check_nonadjacent_channels.json. It also verifies D5,D6<0 and 0<b_r<1 for r=2,...,6. This confirms the arithmetic premise from the stated formulas; it does not independently validate their biological interpretation or the composition identities.

## 5. Positive padding supplies the fourth independent coordinate

Let K=E(u) B(x,y,g) E(w), with u,w in (0,1). Ordinary populations have D_r=J_r=L_r=0. From (1)-(2), with z=uw,

    alpha(K)=z^9 alpha(B),   beta(K)=z^9 beta(B),
    f(K)=u^9 f(B),           h(K)=u^9 h(B).       (7)

Both exponent gaps equal nine: choose(5,2)-choose(2,2)=9 and choose(6,2)-choose(4,2)=9.

Fix z=1/4 and vary u near 1/2, taking w=z/u. Both ordinary passages remain strict. The three coordinates (log alpha,log beta,log|f/h|) retain rank three in (x,y,g) by (6), while log|h| has derivative 9/u in the additional u direction. Thus the four-channel map has rank four at some entirely strict physical tuples. The inverse function theorem gives a nonempty open image in (alpha,beta,f,h), with the translations negative in this chosen neighborhood.

This is simultaneous control of two affine channels from ONE source tuple, not independent fitting of two sources. It does not assert that arbitrary desired digit maps fall inside that open image.

## 6. The old strict dilation-order lock genuinely fails for this pair

Here alpha/beta=b5*b4/(b2*b6). For x=y=1/2,g=1/2,

    b2=3/4, b4=81/512, b5=721/16384,
    b6=9153/1048576,
    b5*b4-b2*b6=3483/8388608 > 0.

At x=0,y=1,g=1/2 the same difference equals -3/128. For a strictly admitted negative example take x=epsilon,y=1-epsilon,g=1/2 with epsilon=1/4096. Each monomial in (4) changes by at most choose(r,2)*epsilon from this boundary value. Since all b's lie in [0,1], the total error in b5*b4-b2*b6 is at most

    [10+6+1+15]epsilon=1/128.

It remains negative. Padding does not change this ratio because the total ordinary exponents on its numerator and denominator are both sixteen. The same two signs were subsequently verified by exact rational substitution in the checker, not floating-point approximation.

## 7. What this changes, and what it does not

The adjacent channels telescope, but nonadjacent forest shapes provide two locally independent affine channels without a universal ordering of their dilations. This resolves a concrete structural question about one proposed reduction interface. It does NOT finish that interface: an open subset of affine pairs is not a proof that any undecidable synchronized word-comparison family can be encoded in it.

The full original reduction still additionally needs an admitted finite observation bank for which EVERY matching source, including alternative cores and arbitrary fresh parameters, yields a valid encoded word. The current algebra is about complete internal kernels; it does not automatically make their signed coordinates legal directly observed scalars. A finite chosen alphabet, a freely engineered postprocessing or two independently chosen private words would not meet that obligation.

Moment/support certificates must enforce a whole-source converse, not merely verify that the chosen letters belong to the model. Exposing a fixed positive pair survival while forcing a finite strict alphabet also invokes the inherited finite-palette word-count bound. Nothing here avoids that bound or supplies a guard that hides it legitimately.

### Specific support-guard check (reuse of a retained obstruction)

One tempting BOTH-mode guard would use COMMON moments of this same word to force the total survival variable onto a finite set S. This is not a per-letter alphabet test. For a natural unexposed COMMON serial word, the total duration is c+sum_i d_i X_i after absorbing shorter arms, with d_i>0 for unequal-arm cells and independent nondegenerate Bernoulli X_i. If there are m such cells, the m+1 partial sums c,c+d1,...,c+sum_i d_i are distinct positive-probability support points. Therefore support contained in S forces m<=|S|-1.

This is the already retained support-size argument in ATOMIC-RESAMPLING-SURGERY-ATTEMPT-20261018-0358.md, not a new source theorem. Applied here, it means that a fixed finite total-support certificate cannot enforce an alphabet of these unequal-arm coding cells while admitting arbitrarily long strings of them. Conversely, equal-arm cells are deterministic in the COMMON channel, so that support certificate alone does not select their inheritance/placement parameters from a finite alphabet. Other I-channel observations could add constraints; this paragraph does not exclude them.

Thus the concrete moment guard tested here either bounds the number of relevant unequal-arm cells or leaves an uncontrolled equal-arm continuum. It does not complete the all-rival language correspondence. In original menus that do not supply the relevant COMMON law, the guard is unavailable in the first place.

## Sources and evidence boundaries

* Original source compiler/reachability: https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md
* Accepted cap-four free-word coding, exact quotient and previous ordered-channel failure: https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-09-dot-g3-reviewed-source-coding-1541z/ACTUAL-FREE-WORD-CODING-AND-PCP-GATE.md
* Scoped newly reviewed adjacent-root route: local PHYSICAL-AFFINE-CHANNEL-RECODING-ATTEMPT.md, coordinator acceptance reported 25 October 2026, 10:21 UTC. Publication link to be supplied by coordinator.
* The generic PFA comparison, not a physical adapter: Paul C. Bell, Theorem 1 and Section 3.1, https://drops.dagstuhl.de/storage/00lipics/lipics-vol132-icalp2019/LIPIcs.ICALP.2019.105/LIPIcs.ICALP.2019.105.pdf . Earlier handoff already screened this literature; no renewed generic hardness claim is made.

The coalescent routing formulas, exchangeability/restriction principles, chronological matrix multiplication and inverse function theorem are standard/inherited ingredients. The exact proposed channel combination and rank calculation require independent review. No exhaustive prior-art claim is made.

Bounded execution: python check_nonadjacent_channels.py, installed SymPy 1.14.0, exit 0. The .log and .json files preserve its scope and exact results. No installation, native build, QE job or original-source recognizer was run.
