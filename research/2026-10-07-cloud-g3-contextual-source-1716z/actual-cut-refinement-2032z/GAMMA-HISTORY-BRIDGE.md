# Actual finite calendar Gamma from one endpoint history

Contributor: Codex, delegated G3/source bridge, 7 October 2026. This is a G6 source adapter prepared for coordinated handoff. **New hand-derived argument and concrete Lean drafts; independent review pending, compiler UNCHECKED.** The prior Eq10/Eq11 source-semantic acceptance does not verify these additions. No compiler, provider or running-freeze edit occurred here.

The question is whether the actual finite calendar's joint endpoint/tree and observed-bin distribution can be obtained from the original finite-state source recursion. Supplying a table named Gamma does not answer that question. This adapter derives that table's mathematical law from the actual source record and keeps the same initial old matrix, boundary operations and physical rate bank.

## Ordinary interior cuts preserve the actual joint law

[ActualFiniteCutJointLaw.lean](ActualFiniteCutJointLaw.lean) contains one definition and seven proposed theorem bodies. For nonnegative finite durations t and v, it establishes the raw endpoint/tag reader at t+v as the reader of the same marked prefix at t followed by its genuine retained-clock future at v. The full Copy cap supplies actual success on the original regular-clock event. The old `same_clock_endpoint_continuation` and the already preserved tag-fold concatenation give the two components of this equality.

`interval_cut_fibre_joint_source_law` pushes this deterministic equality through the original **whole-past** terminal-fibre law. Its right side sums the prefix measure restricted to each endpoint fibre, multiplied by the actual future marked-trace measure at that endpoint. Neither a success-conditioned law nor an endpoint-only renewal law is used. Null fibres retain zero mass. The measurable future reader is proved on the original residual Sum/Sigma clock space before applying the pushforward.

Actual probability and the prior finite observed-fibre regrouping then give

```
segmentJoint(t+v, s, offset, B)
  = segmentJoint(t, s, offset, B).bind
      (d, C) ↦ segmentJoint(v, d, offset+t, C).
```

`calendar_joint_refinement_in_context` applies this row inside any unchanged original calendar prefix and suffix. Repeatedly splitting at the finitely many observation cuts therefore preserves the actual finite Code/tag law. These are analytical subdivisions of an existing source interval: no boundary, vertex, registry draw or rate-bank parameter is introduced. The statement allows an arbitrary measurable finite bin map; constant-bin premises enter only in the next endpoint reader.

## A constant-bin segment has an actual source row

[ActualCalendarEndpointHistory.lean](ActualCalendarEndpointHistory.lean) contains five definitions and six proposed theorem bodies. A word pairs each original operation with auxiliary readout metadata. Its explicit `wordBinContract` requires the bin map to be constant on each interval's open absolute-age interior; boundary labels are unused. At fixed observation cuts the verified BinClock event excludes active ages exactly at those fixed endpoints. This uses the original fixed-horizon source clock law, not a random-cover boundary-nullity argument.

For an interval with tag b, the verified `actual_same_bin_endpoint_fold` on the SAME full-cap trace gives

```
actual interval endpoint/tag row
  = sourceTimeKernel(interval).map
      d ↦ (d, tagUpdate(initialCode, d, b, oldTags)).
```

The unconditional actual raw endpoint source law supplies `sourceTimeKernel`. The tag update retains old joined-pair tags and records new joins from the actual legal-merger endpoint relation. Zero duration is included. An original boundary uses its original `boundaryKernel` and carries the tag matrix unchanged. Original Code retains the actual binary genealogy even when all tags agree.

## Canonical Gamma is a deterministic full-history readout

Induction over the original operations uses the actual unnormalized calendar cons law, the just-derived segment rows, and the original `sourceHistoryLaw` recursion. `endpointHistoryReadout` starts with the supplied initial Code and tags once, then reads the complete vector of operation endpoints. Its final law is

```
actual calendarJoint
  = sourceHistoryLaw(original operations).map(endpointHistoryReadout).
```

`actual_original_gamma_endpoint_history` identifies the preceding principal source's **canonical `calendarJointPMF`** with this law, binning the original real M once at entry. Both sides of the adapter equality are admitted only after actual measurable probability pushforwards; their toMeasure identities show they are the SAME actual calendar pushforward. No desired Gamma equality is an input.

`actual_original_gamma_history_prefix_tv` then applies the verified HistoryPrefix full-history domination to that actual Gamma. For the same endpoint reader and truncation K, the finite-history approximation has total-variation error at most `1 - programMass.toReal`. This is one joint-history bound. It is not an independent error claim for every matrix entry. The original history recursion uses `sourceProgramStep` at every operation; `sourceProgram` is its terminal-state projection and cannot replace the retained vector by itself.

## Evidence and remaining obligations

Exact source pins and declaration inventory are in [HISTORY-SOURCE-INPUTS.json](HISTORY-SOURCE-INPUTS.json). The new drafts are outside the current 155-source formal freeze. Original deterministic cut, Eq10/Eq11, principal calendar and historical provider bytes remain unchanged.

The finite Tag carrier and constant-bin word contract are explicit. Application to a supplied physical old M still uses the existing `ForestDecorates` invariant, SAME actual tree decoder, absent cross-tree pair convention and physical diagonal dates. This law preserves supplied bookkeeping entries even outside joined trees; it does not make those placeholders observable ages. The earlier complete-calendar tail theorem retains its ancestral support and tail-after-last-cut conditions; the accepted hand last-cut extension provides a separate route to that latter premise. These new sources do not formally verify the real identity-bin instance.

The resulting source law is mathematical. It is not yet an executable evaluation of Gamma or a completed physical solver/backend. In particular, numerical certified weights, control/menu/pruning consumers, admitted contextual source reconstruction and their final composition remain separate G6 work. Original unrestricted G3 positive recognition, terminal NO and unbounded-template completeness remain open. No restriction to computable or rational hidden reals is introduced by this adapter.
