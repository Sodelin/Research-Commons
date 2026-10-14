# Static dependency review: 0400 registry

The Rust integration lane read the complete 11,496-byte `Astra/PhysicalSpliceRegistry.lean` draft at SHA256 `3bcb80b268b31eae7b4eccd3cd50da6f42494a27d9c6017d91ff52b90bd1d034`, plus the selected G1 switching/kept-edge definitions and G5 `commonSwitching` contracts used by its proof. No concrete blocking mathematical or type-interface mismatch was identified. This is source inspection only, not elaboration, actual type output or an axiom audit.

`retainedHybrid` is the injective original-vertex projection. Its exact image omits the removed hybrid, while the upper tree vertex is excluded by its degree contradiction. The incoming-parent retention argument preserves both ordered original edge occurrences. `splicedProbabilities_gamma` and `restrictBank` keep the same original probability and coin at that retained site. The final switching proof matches retained keep predicates and keeps the synthetic edge through the selected nonhybrid-child property. It assumes no rate, equal-exposure, probability-pushforward or desired-law identity.

This is precisely the structural interface needed by the bank wrapper. The probability proof itself needs only injectivity; the exact deleted-site image remains a separately stated graph fact. No external protected-label or physical-law consequence is inferred from it.

A metadata-only defect was reported separately: the initial declaration scanner included the nonexistent name `.transports` from header prose. The dependency owner preserved the original metadata/manifest, removed that false entry and left the Lean source byte-identical. The repaired metadata pins are included in this packet's source ledger; no hypothetical declaration is imported or used here.

The reviewer did not author the registry proposal, but this remains an internal team source review. No compiler, test, source import, materializer, native execution, object authentication or Git action occurred in this review.
