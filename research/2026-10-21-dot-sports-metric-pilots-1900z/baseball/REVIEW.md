# Independent review of the baseball pilot

Reviewer: dot (OpenAI-assisted independent review), prepared for Nolan
Date: 21 October 2026
Verdict: Scoped pass as a proposed experiment and ingestion audit. No predictive or novelty validation.

The final MODEL-PROTOCOL.md resolves the principal design objections raised in review: future-200-PA qualification is not the primary cohort; the target has a fixed calendar horizon and includes future zero-exposure players; W and D are explicitly distinguished from PA; the frozen-reference outcome is not called conventional wRAA; and exposure-rate multiplication is not asserted to be an expectation identity. Direct target regression with out-of-fold exposure/rate features is a defensible proposed implementation.

The matched comparison between raw and standardized recent changes is essential. Existing baselines already incorporate recency, shrinkage, contact quality and platoon information. The experiment must show incremental value beyond those features; merely introducing them is not novelty. The protocol preserves this distinction and correctly limits the adjustment to pitcher handedness rather than all context or causal talent.

The evaluation plan preserves temporal ordering and separates tuning from held-out historical scoring. Its proposed percentage thresholds are decision rules, not guarantees. Player-cluster uncertainty with year sensitivity is useful but does not make five seasons a large independent sample. A favorable result would need replication; it would not establish superiority to professional projections without an appropriate as-of comparison.

Required implementation gates remain open: the exact frozen event-weight/denominator table; verified historical feature availability; complete event mapping and reconciliation; construction of the multiyear panel; fitted baselines; and held-out results. No numerical target or score is accepted until these are supplied. The seven-assertion synthetic accounting check in the companion review demonstrates possible selection, mixture, overlap and expectation errors; it does not quantify their size in MLB.

The author-reported one-day audit contains 3,704 pitch records and 931 completed PA after excluding one truncated record. I inspected the report and protocol; I did not independently reacquire the source or rerun that ingestion script in this review. These counts demonstrate a bounded parsing exercise, not forecasting performance. Any separate replay must be reported with its actual execution status. Keep source rows out of a public packet unless redistribution terms are resolved; the present review does not license third-party data.

Prior-art sources checked: [Tango’s Marcel description](https://www.tangotiger.net/marcel/), [Savant expected statistics](https://baseballsavant.mlb.com/expected_statistics), [FanGraphs’ January 2025 Steamer announcement](https://blogs.fangraphs.com/instagraphs/introducing-new-steamer-split-projections-and-more/), and [Statcast CSV documentation](https://baseballsavant.mlb.com/csv-docs). The announcement establishes that context-neutral and platoon forecasts already exist. A bounded search is not an exhaustive novelty audit. Two Baseball Prospectus primary-article requests returned403 and were stopped; their full methods were not evaluated.

This review identifies safeguards for this proposed analysis. It does not allege an established mistake by MLB, professional forecasting systems or baseball researchers generally.
