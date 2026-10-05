# Independent two-source interval-summary ambiguity result

Accepted, bound to final source 3e14552a0d51cb4600dd8f3514140b2f48ffc6362f8c376b614d9a6cec5c9d16 and WITNESS.json SHA256 9224549862edd70495acae269ccdfba78207b46f8d8f24980a6f4d92aceff98c.

I inspected the stable exit-zero terminal and independently reran the exact two-point check under the same 30-second wall/25-second CPU/256 MiB bounds. The output reproduces byte-for-byte, with all 18 complete mean-enclosure containment tests passing. Both coherent source vectors are strictly inside the original physical domain; only rA changes from 1 to 2. The other eight selected mean enclosures are identical, and AA1 enclosures are strictly separated, so the exact mean vectors differ.

Each source's entire selected mean vector lies in the same frozen observed interval box from the one model-generated realization. Therefore every cover that retains all sources compatible with that box must contain both. Its physical rA width is at least 1, above the requested 11/40; normalized width is at least 2/11, above 1/20. Thus the requested all-coordinate target is genuinely impossible for any sound inverse of this particular interval-summary feasible set, regardless of additional subdivision or tighter interval arithmetic.

This does not explain why the existing cover retained the entire original width in every coordinate, nor rule out useful tightening short of the target. It does not show equality of full DNA laws, undermine exact model identifiability, prove an optimal finite-data impossibility or certify confidence coverage. The obstruction concerns the chosen nine-feature Cartesian confidence summary for this fixed realized dataset and target.

No observation, interval, source domain or target changed. There were exactly two predeclared forward evaluations and no adaptive third point or stochastic sampling. Independent deterministic replay introduces no new candidate search. A different statistical summary, tighter justified simultaneous region or additional data requires its own scientific/design and bounded implementation review; none is authorized by this result.
