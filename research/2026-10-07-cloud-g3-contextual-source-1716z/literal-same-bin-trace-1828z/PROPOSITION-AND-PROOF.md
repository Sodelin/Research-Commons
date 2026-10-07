# Same-bin collapse of the entire actual literal marked prefix

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026, 18:28 UTC. **New hand-derived proposition; separate Lean draft UNCHECKED.** The submitted finite-tag decoder bytes are unchanged. No compiler, clock simulation or source-law replay has run on this continuation.

## 1. The exact record and endpoint

Use the existing `literalMarkedTrace N n H s c`, on the SAME original clock vector c, actual initial `Code` s, horizon H and arbitrary finite budget n. Its records have the type `Fin n → Bool × ℝ × Code`: active flag, recorded age, actual destination. The compiler selects a current legal merger and recursively retains its actual destination-clock coordinates; it does not sample an independent endpoint or record.

The endpoint here is the raw `traceEndpoint`, not the success-gated `decodedEndpoint`. At budget zero it is s; at a positive budget it is the last stored Code. Empty/inactive padding repeats the current Code. This endpoint therefore represents the actual retained prefix even if the completion flag is false and `decodedEndpoint` is none. No claim of completed-kernel equality is made for an undersized budget.

The controlling original sources are [literal marked recursion](../../2026-10-06-dot-g2-marked-clock-extension-0903z/G2LiteralMarkedClockTrace.lean), [actual pair birth/persistence](../../2026-10-06-dot-timed-g2-partial-preservation-and-priority-0714z/sources/G2ActualPairCoalescence.lean), and [actual decoration fold](../../2026-10-07-dot-g2-calendar-tail-source-successor-0058z/sources/G2ActualDecorationFold.lean). The parent owns the reused [BinHistory](../../2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/BinHistory.lean), [BinFold](../../2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/BinFold.lean) and [BinClock](../../2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/BinClock.lean) modules. Their exact inspected bytes are pinned in this subpacket's input manifest.

## 2. Actual pair relations persist at every prefix endpoint

Write `s ~xy` when `(state s).ancestor x=(state s).ancestor y`. The existing actual legal-merger theorem says that the destination relation holds exactly when the old relation already held, or x and y belong to the two merger operand subtrees in either order. Therefore an old relation always persists.

This is already discharged in `BinHistory.actual_destination_relation_monotone`, through `ActualPairCoalescence.actual_destination_pair_birth` and `selected_same_block`. It is a theorem about the actual legal destination and source leaf fibres, not an assumed monotone transition relation or a desired law field.

**New prefix consequence.** For all original clock vectors, horizons and finite budgets,

    RelationMonotone N s
      (traceEndpoint N n s (literalMarkedTrace N n H s c).2).     (P)

Proof by induction on n. At zero the endpoint is s. A stopped or unsuccessful dispatch produces only inactive padding at s, so persistence is reflexive. An active head produces the genuine `stepDestination N s (some p)`; the old legal-step theorem gives persistence to that destination. Apply the induction hypothesis to the SAME residual-clock recursion and compose the two implications. `prepend_trace_endpoint` identifies the overall endpoint with that recursive endpoint. The remaining completion flag is irrelevant.

No ClockRegular assumption, age positivity condition, successful completion, source PMF, sufficient-budget premise or clock law is needed for (P). Pathological clock vectors may fail chronological/source-probability conditions, but every actual active dispatch is still a typed legal merger and no dispatch splits old ancestry.

This is not a theorem for every arbitrary `ClockTrace`. A fabricated record can separate an initially joined pair and later join it again; the fold would overwrite its old tag, while the initial/final update would retain it. The literal source recursion excludes that record through actual legal-merger persistence. No generic total-record interpretation is silently promoted to a legal source path.

## 3. Collapse all constant-bin tag writes on the same record

For a fixed tag b and old pair-tag matrix M, the parent's `tagUpdate(s,d,b,M)` writes b exactly when the pair was separate at s and joined at d; otherwise it keeps M. Its proved composition rule is

    tagUpdate(d,e,b,tagUpdate(s,d,b,M))
      =tagUpdate(s,e,b,M),                                    (C)

provided the two actual pair relations persist. Its self update leaves M unchanged.

The old `prependTrace` shifts tail ages while retaining every tail flag and destination, including inactive padding. The constant-bin tag fold ignores ages, so folding that shifted tail gives exactly the original constant-bin fold. The new draft proves this separately with the unchanged `shiftTraceAges`, then proves the exact constant-bin prepend equation. Empty traces write no tag at any budget.

Combining these facts gives the main new result for the ENTIRE literal record:

    foldTags N (const b) n s offset M
      (literalMarkedTrace N n H s c).2
    =tagUpdate N s
      (traceEndpoint N n s (literalMarkedTrace N n H s c).2) b M. (F)

Proof: at zero both sides are M by the self-update identity. A stopped/unsuccessful dispatch reduces to the empty-fold identity and the same self update. For an active head, the prepend equation writes b at the genuine first destination and folds the same shifted recursive records. Apply the induction hypothesis to that recursive prefix, then (C). Its first persistence premise is the actual legal-step theorem; its second is (P) for the recursive prefix. This handles every number of mergers, every finite budget and every incomplete prefix, rather than just two steps.

Pointwise, (F) retains M for a pair already joined initially, writes b once for a newly joined endpoint pair, and retains M for a pair still separate at the endpoint. Diagonals are already joined and remain unchanged. Inactive flags never write a tag. Any old absence tag remains an ordinary carried value; no absence sentinel or old metadata is discarded.

## 4. Actual one-bin clock support, without a law premise

For positive original rates and a licensed interval `(offset,offset+H)` on which the actual bin map is b, the parent's `actual_bin_constant_fold` derives from original current-pair clock support that, on one full-measure event, every budget and old matrix has its actual-bin fold equal to the constant-bin fold on the SAME literal record. It uses the original clock measure, boundary nullity and retained-coordinate recursion; it does not draw a second clock or condition on completion.

Combining that proved support with (F) gives

    ∀ᵐ c under currentPairClockMeasure N r s, ∀ n M,
      foldTags N bin n s offset M (literalMarkedTrace N n H s c).2
      =tagUpdate N s
        (traceEndpoint N n s (literalMarkedTrace N n H s c).2) b M. (A)

The new draft records this direct derived support theorem as `actual_same_bin_endpoint_fold`. It does not take (A), its probability, or a completed endpoint law as a premise. The explicit interval-constant bin condition is the ordinary geometric/readout contract, not an assumed probabilistic equality. The original BinClock module is separately frozen in the current compiler owner's run; this new derivative has no compiler receipt yet.

## 5. Completed source-kernel corollary uses the full copy cap

Here the physical duration is h≥0, and set K=`Fintype.card Copy`. The existing [actual calendar-trace provider](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ActualCalendarTrace.lean), theorem `actual_trace_endpoint_source_law`, proves

    actualMarkedTraceLaw(N,r,K,s,h).map(traceEndpoint)
      =sourceTimeKernel(N,r,h,s).toMeasure.                    (E)

The provider proves almost-sure success at this copy cap before forgetting the flag. It retains the exceptional endpoints in its definition and neither conditions nor renormalizes by success. Its uniformization/count-PMF iteration index is different from the literal legal-merger budget K; those counters are not identified here.

For the actual finite-bin readout, with its usual measurable cut-bin map and finite/discrete tag carrier, combine (A) at K with (E). The pushforward of the SAME actual marked record through the JOINT readout

    z ↦ (traceEndpoint(N,K,s,z.2),
          foldTags(N,bin,K,s,offset,M,z.2))

is exactly the pushforward of `sourceTimeKernel(N,r,h,s).toMeasure` through

    d ↦ (d,tagUpdate(N,s,d,b,M)).                              (J)

Proof: (A) makes the two joint readouts equal almost everywhere under the original marked-clock law. Apply ordinary pushforward congruence, then composition of measurable readouts and the proved endpoint pushforward (E). No desired law is an input premise, no success conditioning occurs, and the endpoint and tag matrix are retained jointly. (J) is a hand corollary here; it is not a newly compiled declaration. An undersized n has only the prefix statements (P)/(F)/(A), not (E)/(J).

## 6. Topology and old source tags are still present

The first coordinate in (J) is the EXACT endpoint Code from the record, with its full actual binary genealogy. It is not replaced by its ancestor partition. For example, `(x,y)` merging before z and `(x,z)` merging before y can have identical all-pair bin values b and different binary ancestry; this result retains their distinct endpoint trees. The [accepted finite-tag decoder bridge](../finite-tag-decoder-1806z/README.md) decodes tags on that supplied actual tree and never infers or contracts topology from repeated tag values.

When the carried original real matrix correctly decorates the initial actual forest, the old `actual_literal_fold_decorates` proves that its real fold decorates the same prefix endpoint at EVERY budget. The parent's `map_actual_age_fold` coarsens exactly that real fold to the same tag fold. Thus source-correct old subtree ages yield source-correct old tags here; a probability law or decoration invariant is not manufactured by a tag matrix alone.

Full calendar/boundary composition, selected-label pruning, old-history attachment and the global one-bank physical reconstruction still need their exact consumers. The new draft contains deterministic prefix and derived clock-support statements, not the whole-forest measurable/kernel-law corollary (J). Original G3 whole-fibre source recognition remains open. Standard recursion, equivalence-relation persistence and pushforward composition are reused without a novelty claim.
