# Exact shadows of quartet support: minimum storage and measurement boundaries

Contributor: Codex `minimal_projection` subagent, MINIMAL-PROJECTION-20260930.
Date: 2026-09-30 UTC. Status: all-size conditional hand proofs and executed
algebra controls. No historical novelty, query-master closure, or Lean claim.

## 0. Verdict and exact target

Nolan's suggestion is mathematically productive: a large table can have a
smaller exact shadow when its entries are constrained. For EXACT-QUERY-01,
the whole displayed quartet-support table has an exact **Theta(n log n)-bit
representation**, even though a fixed quartet-query schedule needs
Theta(n^3) measurements to find a compatible order. These statements are
consistent: stored information and the permitted way of acquiring it are
different resources.

This note exhibits actual encoders and decoders, including a quadratic
distance matrix and a linear number of finite-field moments. It also gives a
source-specific succinct structural code. None of them silently introduces
moment, distance, or whole-block access into the quartet oracle. The adaptive
query master remains open unless its separate algorithm/lower-bound lane
closes it.

Scope: finite binary semi-directed LSA-rootable, outer-labeled planar, galled
networks, arbitrary admitted levels and blob counts. Oracle output is the
complete existential support of distinct displayed quartet topologies.
The output is the full displayed-split union and any compatible circle, not
network topology, probability, switching correlation, or branch lengths.

Inherited source inputs are those pinned in
[SPLIT-COUNT.md](../2026-09-30-root-exact-query/SPLIT-COUNT.md): source opening
into adjacent-copy occurrence trees, capped-port admission, independent local
switching extension, and the full local/global split accounting. They imply
at most `k <= 13n-27` nontrivial splits. No claim here independently reproves
those structural inputs.

## 1. An exact sufficient shadow: splits regenerate every quartet

**Lemma (hand-derived elementary identity).** For a nonempty family F of
binary trees on X and its full nontrivial split union S, a resolved quartet
`ab|cd` belongs to the complete support if and only if there is a split
`A|B in S` with `a,b in A` and `c,d in B`, or the reverse assignment.

Proof: a displayed quartet has an internal edge whose inverse image in the
tree is a nonempty path. Any edge on that path gives a full split inducing
the quartet. Conversely restricting the witness full edge split to four
taxa displays that quartet. Since the four selected taxa give two taxa on
each side, the full witness is nontrivial. Taking the union over F proves
the assertion. QED.

Consequently a stored split union answers any quartet support query in
`O(k)` simple split-membership tests. One need not expand the dense table.
If the user explicitly requests the entire anchored table, writing its
`binomial(n-1,3)` entries already takes cubic output time; the all-quartet
table has quartic output size. A lazy exact support view avoids that expansion.

Given a compatible circle C, index every nontrivial split by its two
nonadjacent boundary gaps. There are

    M = n(n-3)/2

possible gap pairs. Storing C plus the k supported gap IDs costs

    ceil(log2(n!)) + O(k log n) = O(n log n) bits.

It regenerates the entire support table exactly. It also preserves the
**whole** common-order space: an order is permissible precisely when every
stored split is circular. Thus the code is stronger than merely storing
one successful order.

## 2. Minimum total bit complexity

**Theorem (hand-derived, conditional source upper bound).** Worst-case exact
storage of the split-plus-order target, and hence of the complete support
table on this class, is Theta(n log n) bits.

The upper bound is Section 1 and `k <= 13n-27`. For the lower bound the
admitted class includes all `(2n-5)!!` labeled binary trees. Different trees
have different full split systems, and different complete quartet tables.
The split systems determine the trees: their edge bipartitions reconstruct
the compatible-tree hierarchy. Therefore an exact code must distinguish
at least `(2n-5)!!` outputs, requiring

    log2((2n-5)!!) = Omega(n log n)

bits in the worst case. A variable-length code changes this by at most an
additive constant for the maximum-length counting argument. QED.

This is a minimum **bit** boundary. It does not say that O(n log n) legal
quartet queries suffice to acquire the code.

## 3. A concrete quadratic shadow: a split-distance matrix

Choose a compatible C and define, for distinct x,y,

    d(x,y) = 2 + sum over S in the nontrivial union of delta_S(x,y),

where `delta_S(x,y)=1` exactly when S separates x,y. Set `d(x,x)=0`.
The constant 2 is the contribution of all singleton splits with unit
weight. This is a genuine circular split metric, with all present
nontrivial coefficients equal to one.

For disjoint adjacent C-gaps `(a,b)` and `(c,d)` in cyclic orientation,
the full split with side `b,...,c` has coefficient

    w = [d(a,c) + d(b,d) - d(a,d) - d(b,c)] / 2.

**Direct proof of this inverse.** A circular split contributes to the
bracket only if it separates a from b and c from d. Since the pairs are
adjacent, these separations force its two boundaries to be exactly those
two gaps. Their intervening split contributes 2, and every other split
contributes zero. Singleton contributions cancel. QED.

Thus C and the `binomial(n,2)` matrix entries recover the entire split
union with O(n^2) local arithmetic operations. Each entry is an integer
at most `k+2=O(n)` and needs O(log n) bits. The matrix is an exact
quadratic-size shadow, although the gap list in Section 1 is smaller.

This inverse and the Kalmanson/circular-split equivalence are classical,
not claimed new. Gorbounov and Kazakov, arXiv:2501.01383v1, Section 3.2,
state the adjacent-coefficient formula; Forcey, arXiv:2108.00550,
Theorem 3.7, gives the classical equivalence and discusses uniqueness.

The matrix above is constructed from the **full union**. It must not be
confused with an average gene-tree distance, an arbitrary anchor-derived
distance, a resistance matrix of the original source network, or a
distance available for free from one quartet measurement. Those are
different acquisition/weighting contracts.

## 4. An exact linear sketch: O(n) finite-field moment symbols

This is a constructive answer to the request for lower-dimensional
measurements that can be projected back exactly. Its measurements are
stronger than the registered point oracle, explicitly identified below.

Supply C, enumerate its M possible nontrivial gap-pair splits as
`1,...,M`, and let `v_i in {0,1}` indicate membership in the full union.
Choose a prime `p > M`. For `j=0,...,K`, where
`K=min(M,13n-27)`, request the aggregate moment

    s_j = sum(i^j v_i, i=1,...,M) mod p.

These are **linear** maps of the sparse gap-indicator vector, over F_p.
Since p>M and k<=M, `s_0=k` as an ordinary integer; there is no modular
count ambiguity. The first k positive moments then determine the support.

Let `e_0=1` and recursively compute

    e_j = j^(-1) sum((-1)^(l-1) e_(j-l) s_l, l=1,...,j),
    j=1,...,k.

Every inverse exists because `j<=k<p`. Newton identities show that

    P(t) = t^k - e_1 t^(k-1) + e_2 t^(k-2) - ... + (-1)^k e_k
         = product(t-i, i with v_i=1)

over F_p. Evaluating P on `1,...,M` recovers precisely the selected IDs,
which are distinct residues. This proves exact reconstruction without
floating-point approximation, probability of collision, or unrestricted
precision. The empty-support case gives P=1 and no roots.

The decoder uses O(k^2+Mk) field operations with the elementary recurrence
and root scan. With k=O(n), M=O(n^2), this elementary implementation is
O(n^3); it is a storage/sufficient-measurement result, not an asserted
linear-time decoding result. The code uses k+1 moment symbols after k is
known, at most K+1=O(n) symbols nonadaptively. Bertrand's theorem permits
`p<2M` for M>=2, so each symbol has O(log n) bits and the total is
O(n log n) bits.

Moment/syndrome/Prony reconstruction is established prior machinery.
Ben-Or and Tiwari (1988), DOI 10.1145/62212.62241, is classical sparse
interpolation; recovery from power sums has a substantial literature.
This explicit binary equal-amplitude finite-field decoder is derived
here to make the exact acquisition boundary reviewable, not as a claim
of algorithmic novelty.

**Acquisition restriction.** `s_j` aggregates potentially every one of
the M support bits. The registered oracle returns only a single quartet's
support. It does not return this sum. Computing the sum from point
answers first is merely postprocessing and does not eliminate those
measurements. With C supplied, the existing legal rectangle-group-testing
algorithm already acquires the sparse support in O(n log n) point queries.
The unresolved issue is finding C or recovering order and support jointly.

## 5. A still smaller unlabeled structural code

The source representation offers a useful minimization beyond storing
an arbitrary sparse subset of M positions. Let C be the cyclic leaf
order induced by a source plane embedding. This is **some** compatible
circle, not necessarily an arbitrary separately supplied compatible
circle. The encoding is given the source representation; acquisition
from queries is a separate problem.

Let R be the reduced plane tree of blobs, with n taxon leaves and q
interior vertices. As in SPLIT-COUNT.md,

    q <= n-2,
    sum(m_B) = n+2q-2 <= 3n-6,
    sum(M_B) <= 2 sum(m_B) <= 6n-12.

For each retained branching blob B, `m_B` is its number of ports and
`M_B<=2m_B` the number of physical occurrence leaves. Encode:

1. The ordered plane shape R, with taxa attached in the order C.
2. At each B, m_B flags saying which local ports occur twice.
3. At each B, the ordered binary occurrence-tree shape on those M_B
   physical leaves.

The local port labels are already fixed by the incident edges of R and
their cyclic order; adjacent duplicate flags fix the local physical leaf
sequence. A deterministic rooting at a distinguished occurrence gives
a standard ordered binary-tree shape code of O(M_B) bits. Ordered-tree
parentheses and self-delimiting per-node records use O(n) bits in total.
Long two-port chains are omitted because the inherited split-accounting
lemma proves they contribute no new full taxon split.

**Decoder.** Add the bridge splits of R. For each internal occurrence-tree
edge, enumerate choices of the at most two duplicated port labels
straddling its boundaries; add every resulting nontrivial local split
after replacing ports with their taxon components in R. Independent local
switch extension and the inherited global split-accounting lemma prove
both inclusions. Deduplicate. The output is exactly the full split union.
Section 1 regenerates all quartet support. A straightforward implementation
that explicitly constructs taxon sets is polynomial, O(n^2) with bitset
word costs accounted separately; no performance benchmark is claimed.

Hence, **conditional on a source embedding order**, O(n) additional bits
encode the target's unlabeled structure, and C costs O(n log n) bits.
This explains structurally why the target information can remain small
even with arbitrary source reticulation levels and blob chains.

The order condition must not be weakened silently: this note has not
proved that every compatible circle admits an adjacent-copy source
representation producing that same union in that circle. The gap-list
and moment encodings in Sections 1 and 4 do work for every compatible C.

The O(n) conditional scale cannot in general be reduced to O(1) bits:
already the fixed-circle binary tree subclass contains the Catalan-sized
family of distinct plane binary tree shapes. Equivalently root at one
fixed taxon and let the remaining leaves have their fixed linear order;
the ordered full binary tree shapes give `Catalan(n-2)` distinct compatible
unrooted trees. Its logarithm is Omega(n). Thus the source-embedding
conditional structure scale is Theta(n) bits. This conditional result
is separate from the total Theta(n log n) labeled-output scale.

## 6. What the cubic lower bound still rules out

The admitted pendant-three-leaf witness in
[adaptive-adversary-nonadaptive-order.md](adaptive-adversary-nonadaptive-order.md)
proves that any fixed coordinate-query schedule must cover every triple.
Its size is at least `binomial(n,3)/4`. This holds even when only **one**
compatible circle is requested, with no full output.

Therefore no transformation performed **after** a fixed collection of
O(n^2) point queries can repair missing information. This includes complex
relabeling, Fourier postprocessing, hashing, learned decoders, nonlinear
packing, and exact matrix code. The indistinguishable input trees have
the same collected answers, so every postprocessor receives the same
input and fails on at least one witness.

There is an additional source-specific restriction: the admitted
five-taxon level-two fixtures in
[ANCHOR-COLLISION.md](../2026-09-30-root-exact-query/ANCHOR-COLLISION.md)
have equal **entire fixed-anchor** tables and different full split unions.
Thus no projection of that anchored cubic table, of any dimension or
precision, determines the complete split union. It still determines the
common-order space through the inherited interval theorem. Unrestricted
additional queries are essential for the full output.

Neither result prohibits legal answer-dependent measurements. The
nonadaptive lower bound is precisely the reason to attack adaptive
measurement selection rather than treating small storage as an algorithm.

## 7. Complex numbers and dimension accounting

A complex number has two real coordinates. If an arbitrary real vector
with n^3 independent coordinates is linearly projected to n^2 complex
coordinates, real rank is at most 2n^2. For n>2 the kernel is nontrivial,
so exact reconstruction of all such arbitrary vectors is impossible.
The source quartet data are not arbitrary independent real coordinates;
Sections 1-5 exploit their restricted combinatorial structure.

One scalar can encode any finite binary table as
`sum(2^i v_i)` if arbitrary integer precision is free. That needs as many
bits as the original arbitrary table. Packing two chunks into real and
imaginary parts changes their placement, not the information count.
Likewise z -> z^2 is not even injective on unrestricted complex numbers,
since z and -z have the same square. A domain restriction can remove
that ambiguity, but supplies no automatic query savings.

Complex-root Vandermonde compressed sensing is relevant prior work, but
the precision and access assumptions must be charged. Ardestanizadeh,
Cheraghchi and Shokrollahi, arXiv:0901.2147, explicitly study total accurate
bits as well as measurement count; their Vandermonde rows have roots on
the complex unit circle. Das and Vishwanath, arXiv:1303.3943, show benefits
of finite-alphabet coding. Section 4 chooses finite fields to make the
exact bit and collision accounting transparent.

The promising interpretation of Nolan's request is thus: identify the
small intrinsic combinatorial structure, then find permitted measurements
that expose it efficiently. The first half is established here. The
second remains the all-level adaptive-query master.

## 8. Executed controls

Run `python minimal_projection_controls.py`; receipt:
[minimal_projection_controls.json](minimal_projection_controls.json).

| Check | Executed result |
|---|---:|
| Exhaustive sparse moment decoding for 1<=M<=12 | 8,190 supports |
| Random sparse moment decoding for 4<=n<=60 | 285 supports |
| Circular unit-distance inversion | 285 split systems |
| Saved admitted level-two support-table regeneration | 10 quartet answers |

All passed. The random circular split systems need not be source-admitted;
they control the algebraic identities, not a source lower bound. The two
source fixtures were read from the inherited actual graph/switching
receipt, so this script independently checks their encoding/regeneration,
not their graph admission anew. The succinct structural codec in Section 5
is proved conditionally; it was not implemented. No aggregate moment
measurement was executed against a biological or legal quartet oracle.

## 10. Primary bibliography and prior boundary

- Keijsper, J. C. M., and Pendavingh, R. A. (2014). Reconstructing a
  phylogenetic level-1 network from quartets. DOI:
  https://doi.org/10.1007/s11538-014-0022-z ; arXiv:1308.5206.
  Established GF(2) quartet/order representation; separate from the
  all-level exact point-query optimum.
- Ben-Or, M., and Tiwari, P. (1988). A deterministic algorithm for sparse
  multivariate polynomial interpolation. DOI:
  https://doi.org/10.1145/62212.62241 . Primary author/institution record:
  https://research.ibm.com/publications/a-deterministic-algorithm-for-sparse-multivariate-polynomial-interpolation .
- Ardestanizadeh, E., Cheraghchi, M., and Shokrollahi, A. (2009).
  Bit Precision Analysis for Compressed Sensing.
  https://arxiv.org/abs/0901.2147 . Precision-sensitive complex Vandermonde
  recovery, not a replacement for a restricted point oracle.
- Das, A. K., and Vishwanath, S. (2013). On Finite Alphabet Compressive
  Sensing. https://arxiv.org/abs/1303.3943 . Coding-based finite-alphabet
  sparse measurement/recovery.
- Forcey, S. (2021 preprint; 2023 journal publication). Circular planar
  electrical networks, split systems, and phylogenetic networks.
  https://arxiv.org/abs/2108.00550 ; SIAM Journal on Applied Algebra and
  Geometry 7(1), 49-76. Kalmanson/circular split representation.
- Gorbounov, V., and Kazakov, A. (2025 preprint). Electrical networks and
  data analysis in phylogenetics. https://arxiv.org/html/2501.01383v1 ,
  Section 3.2, adjacent finite-difference split coefficients. Electrical
  specializations in that paper are not assumed here.

The search covered primary compressed-sensing, sparse-interpolation and
Kalmanson sources before choosing the algebraic sketch. It was bounded
and was not an exhaustive systematic novelty review. Classical shadows
are used as tools; a priority claim for the all-level succinct specialization
would require a separate prior audit.

## 11. Process integrity

The exact oracle and target were read before proposing projections.
Source facts were pinned and remain visibly inherited. Algebraic identities
have explicit proofs and finite controls. Representation, acquisition,
decoding time, output expansion and precision are charged separately.
The principal process limitation is that the structural codec inherits
the occurrence-tree/port source audits and was not independently implemented.
No clinical GRADE or review-quality score is assigned to a mathematical
conditional proof; the appropriate grade is internally checked hand proof,
with source dependencies and executable algebra controls.

## 12. Robustness and counterfactuals

The exact gap, distance and moment reconstructions survive arbitrary
finite levels and blob counts once a compatible circle and full split
union are available. Their storage bounds require the inherited linear
source count. If that count failed, the same identities would hold but
their linear-sized code guarantee could fail. If exact absence were
replaced by finite sampling, every exact support claim would need the
separate observation owner's probability/margin argument.

The succinct O(n)-bit conditional structural code additionally needs a
source embedding order and independent local switching extension. An
arbitrary compatible order cannot be substituted without another lemma.
Moment collision avoidance fails if p<=M or the count wraps modulo p;
the stated p>M condition repairs both. The nonadaptive impossibility
ceases to apply when queries depend on earlier answers, or when an
independently justified stronger block-measurement oracle is provided.

No effect-size pooling, heterogeneity statistic or meta-analysis applies
to these deterministic identities. The mathematical counterfactual above,
rather than artificial numeric confidence, is the relevant robustness test.

## 13. Zotero integration

Import the six primary records by DOI/arXiv ID. Suggested tags:
`Research-Commons`, `EXACT-QUERY-01`, `compressed-sensing`,
`measurement-access`, `finite-alphabet`, `circular-splits`,
`Kalmanson`, `precision`, `prior-art`. Link this note to the source-count
audit and nonadaptive order witness; distinguish an established prior
algorithm from the present hand-derived specialization and from the
unresolved point-query master.

## 14. Restart obligation

Do not spend more effort compressing a dense table merely to report
storage improvements as query savings. Continue the jointly adaptive
order/split acquisition problem, using the O(n)-sized source structure
as its latent target. A valid next theorem must specify how its chosen
quartet queries expose that structure, prove the bound for the actual
complete-support oracle, and handle every admitted finite level/blob count.
