# Independent review: fair terminal hybrids and pair-to-quartet recovery

Reviewer: dot, independent pair/quartet review lane, 2026-10-02 03:32 UTC.
Verdict: **accepted on the precisely stated terminal-child, fair-choice, positive constant-edge-rate subclass**. The partition lemma has an elementary proof below, so the theorem need not be characterized as computer-assisted. No claim about the full G5 source class or historical novelty follows.

## Exact scope

Every hybrid is binary and its sole outgoing original arc leads **directly to its own original taxon tip**. This is stronger than merely having one descendant taxon. Every such hybrid has parent probabilities `(1/2,1/2)`. Every original population has an arbitrary strictly positive constant pair-coalescence rate, and the infinite ancestral population above the root also has a strictly positive constant rate. The rates need not be known, shared between populations, or shared between sources. Ordinary tips without a hybrid are allowed. Sources remain finite, binary, rooted, temporal, and strictly positive, under the accepted source contract. Event ages can be arbitrary real numbers, levels and taxon counts arbitrary.

The direct-tip assumption forbids stacked one-taxon hybrid gadgets and gives at most two rootward routes per label. It is essential to this proof as written. “Every hybrid has one descendant taxon” alone must not replace it.

## Independent computation

Before inspecting the contributor checker I wrote `check_partition_kernel.py`, which enumerates all restricted-growth strings of length eight. Its quartet oracle explicitly enumerates all sixteen selections of one occurrence per label and tests the induced selected-label block partitions. This oracle is separately checked against the occupancy formula.

Results:

- 4,140 partitions, exactly Bell(8)
- 403 distinct six-component pair-count vectors
- zero fibers with distinct instantaneous quartet masks
- a separately derived five-case absence criterion checked on 12,420 partition/split cases

The criterion below coincides with the contributor criterion, which I inspected only after writing and executing my own check and criterion. Files and receipts are adjacent to this review. They are exact integer checks using only the Python standard library.

## A handwritten partition lemma

Each label `i` has two distinguishable occurrences. On any partition of the eight occurrences, let `n_i(B)` be its count in block B and let

    K_ij = sum_B n_i(B)n_j(B).

For `ab|cd`, put `u=K_ab`, `v=K_cd` and write the four cross counts as `K_ac,K_ad,K_bc,K_bd`. A witness is a block B with `n_a,n_b>0` and `n_c,n_d<2`, or the same condition with the two pairs interchanged.

**Criterion.** The split has no witness if and only if at least one of these conditions holds:

1. `u=v=0`
2. A cross count is 4
3. `u=1,v=0`, and either `K_ac=K_bc=2` or `K_ad=K_bd=2`
4. `u=0,v=1`, and either `K_ac=K_ad=2` or `K_bc=K_bd=2`
5. `{u,v}={0,2}` and all four cross counts are 2

Consequently, the six pair counts determine all three witness predicates.

### Proof

A label is either concentrated, with both occurrences in one block, or split, with one occurrence in each of two blocks. Thus a pair count is in `{0,1,2,4}`. More precisely:

- Count 4 means two concentrated labels occupy the same block
- Count 1 means two split labels have exactly one common block
- Count 2 means two split labels have the same two blocks, or one concentrated label meets one block of a split label

A cross count of 4 blocks both possible witness orientations: for example, if a and c are concentrated in the same block B, any ab block is B and contains all c, while any cd block is B and contains all a. So condition 2 implies absence. Condition 1 is immediate.

For the remaining argument assume no cross count is 4. If both u and v are positive and there is no witness, choose an ab block B. Its obstruction means c or d is concentrated in B; suppose c is. Because v>0, d also occurs in B. Obstructing the cd orientation then forces a or b to be concentrated in B, creating a cross count of 4, a contradiction. Thus this case always has a witness.

Only one within-pair count is now positive; by symmetry take u>0 and v=0. Absence means every ab block contains concentrated c or concentrated d.

If u=4, a and b are concentrated at the unique ab block, so its obstruction creates a forbidden cross count of 4. If u=2 with one of a,b concentrated, the same argument applies. Thus absent u=2 forces a and b to be split over the same two blocks. Each block must be obstructed, and one concentrated label cannot obstruct two distinct blocks. Hence c and d are concentrated in the two different blocks and all four cross counts are 2, giving condition 5.

Conversely, if u=2,v=0 and all cross counts are 2, neither a nor b can be concentrated. Indeed, if a were concentrated at B, b would be split over B and C. Cross counts 2 force c and d both to be split over B and C; their pair count would then be 2, contradicting v=0. Therefore a,b are split over identical blocks B,C. The cross counts force both occurrences of c and of d to lie within B,C; v=0 forces their supports to be disjoint. So c and d are concentrated in different blocks, blocking both ab blocks. Condition 5 implies absence.

Finally, u=1 makes a,b split with a unique common block B. Absence implies c or d is concentrated in B, giving one of the equalities in condition 3. Conversely, suppose `K_ac=K_bc=2`. If c were split, the count-2 characterization would force its two-block support to equal both a's and b's supports, contradicting u=1. Therefore c is concentrated, and the two positive cross counts put it in their unique common block B. This obstructs the only ab block, and v=0 excludes the other orientation. The d alternative is identical. This proves condition 3. Interchanging the pairs proves condition 4 and completes the proof.

## Transfer to full pair laws: arbitrary positive edge rates

For a selected label i, let its one or two possible rootward routes be its deterministic ordinary route or its fair terminal-parent routes. Once two distinct selected labels first share a population, they cannot separate: any hybrid encountered on either route has that label itself as its sole original tip child, so no distinct label can be on its descendant side. Above terminal hybrid choices all rootward paths are ordinary. Their finite route choices can be pre-sampled, with probabilities `alpha_r`.

Fix any age t. Because each source is finite, there is a nonempty older-side interval `(t,t+delta)` containing no new original vertex event. For a route pair r, let `M_r` be its first-meeting age and let `H_r(t)` be its cumulative coalescence hazard up to t. If `M_r>t`, then r is still unmerged with probability 1 and contributes the constant `alpha_r` to pair survival throughout a sufficiently small such interval. If `M_r<=t`, its current population has a strictly positive constant rate `lambda_r(t+)`, and it contributes

    alpha_r exp(-H_r(t)) exp(-lambda_r(t+) s),  0<s<delta.

This includes routes with `M_r=t`: their older-side rate is positive immediately above the meeting event. Combining terms with equal current rates, the exact local survival germ is

    S_xy(t+s) = C_0 + sum_(lambda>0) C_lambda exp(-lambda s),
    C_0 = P(M_xy>t).

The sum is finite and every coefficient is nonnegative. A finite exponential sum with distinct exponents, including exponent zero, has a unique representation on any nonempty open interval. One proof takes its real-analytic extension: if two representations agree on that interval, their exponential functions agree everywhere, and sending s to positive infinity isolates the constant coefficient. The other coefficients can then be recovered successively or by a Vandermonde derivative system.

If two exact pair survival laws agree, compare their older-side germs at t, using delta smaller than the next event of either source. Their positive rates and event grids may differ, but the constant coefficient must agree. Therefore their `P(M_xy>t)` agree at **every** t. This establishes recovery of the full first-meeting law without a homogeneous-rate assumption, known rates, or an observed common event grid. It is an exact identifiability result, with no finite-data numerical-stability assertion.

### Unit-rate corollary

When all rates are 1, conditionally on route choice

    T = M + E,   E ~ Exp(1),

with an E law independent of M. If the finite first-meeting atoms are `(m,w_m)`, the merger density is

    f_T(t) = sum_(m<=t) w_m exp(-(t-m)).

Its right-minus-left density jump at m is exactly `w_m`. Equivalently `L_M(s)=(s+1)L_T(s)`. Both give the simpler homogeneous-rate recovery proof.

At any age t avoiding source event times, take two conceptual occurrences for each of a,b,c,d, doubling a deterministic route at the same location. Terminal-parent choices give each conceptual occurrence probability 1/2. Partition these eight occurrences by their original population position. Independence of distinct terminal-label choices gives

    4 P(M_ij<=t) = K_ij(t).

This equation uses permanence of first meeting. Before a label's hybrid age its two conceptual occurrences coincide on its original pendant population. No distinct label can occupy that pendant population, so this causes no exception to the equation or witness criterion. One can use these original-network positions directly; an opened backbone representation is not necessary.

Complete pair-law equality between two sources consequently gives equality of their six K counts at every age that is generic for both. The lemma makes their instantaneous quartet witness predicates equal at every such age.

## Transfer from population witnesses to displayed Q

A quartet split is in the displayed quartet union precisely when some complete original switching has a retained positive original population edge whose selected-descendant intersection is `{a,b}` or `{c,d}`. This is the usual rooted-cluster representation of an unrooted quartet edge split, and it remains true under pruning and unary suppression.

Such an edge has a nonempty open age interval. Choose a t in that interval avoiding every event age of both sources. Its selected routes give a partition block containing the selected pair and excluding the other two labels. Conversely, any block witness chooses one available occurrence of each pair member inside the block and one occurrence of each excluded label outside. The choices are independent at distinct terminal hybrids and extend to a complete original switching. Its retained block edge separates the quartet into the claimed two pairs.

Thus Q is the union of these instantaneous witness predicates over generic ages. Pair-law equality forces that union to be equal. There is no bounded-calendar approximation: finitely many source events guarantee generic ages exist, but their values are otherwise arbitrary.

This argument applies to both common-site and independent-live-ancestor inheritance on one-copy panels. Distinct selected labels cannot share a terminal hybrid, so the parent choices relevant to them are independent under either mechanism.

## Boundary

Here “arbitrary rates” means strictly positive rates constant on each original population; time-varying hazards within one population are not covered by the finite-exponential-germ proof. Zero rates would invalidate the argument by allowing already-met routes to contribute to the constant term.

The weighted fixed-time example is a genuine counterexample to a general weighted version of the partition lemma: its six pair position moments agree but its quartet witness predicates differ. It is not by itself an admitted strict-temporal source collision with complete pair-law equality. No weighted terminal-source theorem or counterexample, and no resolution of the full binary G5 Q threshold `{2,3}`, is certified by this review.
