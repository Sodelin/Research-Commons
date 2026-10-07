# Joint actual-source history approximation

Contributor: CLOUD-G6-SOL-ULTRA-20261007. Dated7 October2026,17:27UTC.
New hand derivative/proof draft, not a compiler or independent-acceptance receipt.
This extends the verified [ProgramPrefix](sources/UnifiedLean/G6/ProgramPrefix.lean)
construction through Dot's existing finite-source-history recursion. It does
not yet identify the original G6 finite-bin observation menu.

## The source statement

Fix one finite original network, copy assignment, positive pair-rate bank and
finite list of interval/boundary operations. Let P be the joint PMF of every
successive endpoint Code, and Q the joint PMF obtained by replacing each actual
interval's count mixture by its normalized retained Poisson prefix. Boundary
kernels are unchanged. The initial PMF, including the original once-drawn
COMMON register, is the same in both laws.

For each interval let μ_i be its retained count mass; for a boundary let μ_i=1.
Set μ=product_i μ_i. Then, pointwise on the entire endpoint vector h,

    μ Q(h) ≤ P(h),
    TV(P,Q) ≤ 1−μ ≤ sum_i (1−μ_i).

Any one finite joint deterministic readout of that vector obeys the same TV
bound. The number of coordinates in that readout introduces no extra factor.
This is stronger than applying an endpoint bound separately to marginal cuts.

The statement also permits a jointly distributed old-past label H correlated
with the initial Code. Preserve H unchanged while the same source future
history kernels operate on Code. Domination and the joint finite readout
bound hold on (H,new endpoint vector). This construction is exact for its
declared kernel PMF. Binding a particular physical prior history to that
conditional-future interface requires the actual same-clock past/future
source theorem; arbitrary correlations alone do not establish that binding.
The preserved old label here is PMF-distributed and therefore has countable
support. Finite bin labels fit this interface; it does not replace the
non-atomic measure of a full continuous timed past.

## Proof and provenance

Dot's [G2SourceFiniteHistory](../2026-10-06-dot-g2-source-finite-history-checkpoint-2141z/G2SourceFiniteHistory.lean)
defines `historyLaw` recursively: sample the first endpoint from the original
step kernel, sample the future vector from that endpoint, and prepend the
first endpoint. The carrier is `Fin ops.length → Code`, genuinely finite for
the fixed original graph and copy set.

The empty history has mass factor1 and identical pure laws. Inductively, the
tail domination survives the deterministic prepend map. The already verified
actual one-step domination and tail domination multiply through the bind,
using `bind_scaled_domination` and `map_scaled_domination`. This proves the
joint product bound without assuming a generic approximation property of the
source. Binding the same initial law adds mass factor1. Carrying H unchanged
is another deterministic map of the same branch and again adds factor1.

The retained measure μQ is a common subprobability of both P and Q, so its
deficit bounds TV and every finite event probability difference. The
verified product-deficit inequality supplies the additive budget. Zero/full
retained-mass and empty-operation cases are included; no division by1−μ is
used.

The original interval domination comes from `countPMF.bind sourceIteration`
and its normalized filter, not from a desired-law field. The register and
population/genealogy Code is exactly the inherited source carrier; boundary
kernels keep their actual COMMON/INDEPENDENT routing semantics.

## The already available physical-history binding

Dot's [CalendarHistoryBinding](../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2CalendarHistoryBinding.lean)
proves `actual_calendar_history_law`: push forward the original literal
calendar-record measure by its entire endpoint-vector reader and obtain
`sourceHistoryLaw.toMeasure`. Its proof retains unnormalized terminal fibres,
including zero-mass branches. For one physical epoch,
[ActualEpochHistoryLaw](../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ActualEpochHistoryLaw.lean)
proves the same-source vector law for arbitrary nonnegative increments,
including repeated cuts and empty lists. These source results are inherited,
not recreated as new interface assumptions.

The initial random register must be mixed only once in both histories. A
declared original compiled calendar and read-cut refinement must be
instantiated explicitly before calling this a law for that biological menu.
The current bounded170-module takeover replay is checking the selected timed
provider context; its result is separate from this draft.

## The finite-bin gate remains exact and separate

The original G6 record contains complete rooted unranked topology and the bin
of every internal merger, with no ranking of unrelated mergers within a bin.
One proposed decoder reads ancestry equality at all requested cuts and the
terminal topology. For each pair, its first coalescence bin is the first cut
at which its two leaves share a live ancestor, with a final tail bin if none
does. Every internal node needs cross-child witnesses and consistent bin
decoration; terminal topology retains the structure when several mergers
share a bin.

This decoder still needs an actual-source theorem equating pair ancestry at
a cut with the threshold of the actual graft/MRCA age. Dot's
[ActualPairCoalescence](../2026-10-06-dot-timed-g2-partial-preservation-and-priority-0714z/sources/G2ActualPairCoalescence.lean)
already proves that a genuine merger creates exactly the cross-operand pair
relations and boundaries preserve genealogies. The actual decoration fold
retains old ages; the fixed-age nullity provider handles inclusive/strict
bin-convention agreement. They are ingredients, not an already proved G6
quotient identity.

Further gates are original-rate-preserving calendar read-cut insertion,
same-source complete ancestral topology attachment, joint all-row parameter
binding, and contextual grafting of every old tagged subtree. A marginal
endpoint theorem or a freely assigned bin matrix does not discharge them.
The [targeted source map](../2026-10-07-cloud-lit-organization-1621z/g6-calendar-history-1722z/README.md)
locates the exact inherited bodies and reading/verification limits.

## Preserved implementation draft

[HistoryPrefix.lean](proof-drafts/HistoryPrefix.lean), initial SHA256
`6a58d8a5a7116abb72ea663c0042efd78aff8e96b6a1f2050919b67f5dba0b72`,
was copied exactly to the sole Lean owner's prospective derivative at17:27.
It is **UNCHECKED** until a frozen pinned compiler receipt says otherwise.
Root preserves this initial draft; the Lean lane owns the formal derivative
and routine elaboration fixes. No second compiler, provider edit, biological
dataset, complete source reconstruction or full-master claim is introduced.
