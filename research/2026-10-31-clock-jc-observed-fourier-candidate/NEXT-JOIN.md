# Exact subsequent join (source analysis, not a proved endpoint)

The frozen observed-Fourier candidate does not require the pending complete-clock candidate. To join them after exact compilation:

1. Use accepted `JC69Source.actual_original_point_support` to obtain `GoodPoint` almost everywhere under the original completeCalendarTraceLaw. This already includes terminal cardinality and the original matrix's timed bound; do not assume either anew.
2. Unfold `conditionalKernel` on that support. Accepted `JC69Observation.actual_original_label_probability` identifies its real-valued mass exactly with the original-label rootLikelihood. Its actual TimedBound witness comes from GoodPoint. This avoids making a nonnegativity claim for arbitrary off-support matrix/leaf-age data.
3. Convert the finite conditional site product using ENNReal.toReal_prod, then substitute the per-site equality. This is exactly locusLikelihood with all sites on the same original tree. No sitewise resampling or product of mixtures occurs.
4. Therefore the finite signed conditional-kernel sum in the observed-Fourier candidate equals the labelledTreeFourier in the complete-clock candidate almost everywhere. To substitute its nested endpoint-fibre/root-clock expression, use the existing completeCalendarTraceLaw decomposition into endpoint-fibre/product/pushforward measures and actual completeAncestralTraceLaw. Keep endpoint fibre masses; do not normalize the individual fibres or replace root clocks by a new measure.
5. Integrability on the observed side is already derived from actual PMF masses in the candidate. Transfer via the exact almost-everywhere identity; do not introduce assumed integrability of a guessed exponential-polynomial expansion.

This is a pinned-source implementation route, not an accepted theorem or an additional conditional provider. Actual source hashes remain those in BUILD-REQUEST. The full scientific finite representation and manuscript bounds are untouched.
