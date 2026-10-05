# Truth-report API repair gate

Accepted for one corrected arithmetic-only attempt and its readout, bound to new manifest 2cb9e5bbbea22a053ff060bdeb33326b08ac27819612006a83e8a594b1489741 and correction plan 559c8191c19460533f4d5bd4a6360874361a583842fe795e740f9d3bedaa5efc.

The original Stage C source manifest f13128d7 and all its successful composition evidence remain immutable. Stage D attempt 1 failed because the adapter called internal evaluate(), whose Fraction/interval return is not the public JSON report schema. This source-review omission is now explicit. Its empty truth output and failed terminal/readout are preserved, with no accepted truth result inferred.

The sole arithmetic API correction calls report(parameters,128), which invokes the same pinned evaluate computation and serializes the established rational interval schema. I inspected the one-line change, authenticated every original archived source and new manifest entry, and independently reran all 36 unit/mock tests including the serialization regression. Corrected readout separately binds the old composition release and new truth release rather than rewriting provenance.

Only fresh truth-attempt2 may execute at the unchanged 512 MiB/30-second bounds, followed by the bounded corrected readout. No simulation, seed change, observation filtering, confidence reconstruction run or inverse rerun is included. Failure again preserves the attempt and stops. Independent final truth arithmetic and complete numerical-chain replay are required before result acceptance. This is an API/reporting repair, not another sampled realization or statistical retry.
