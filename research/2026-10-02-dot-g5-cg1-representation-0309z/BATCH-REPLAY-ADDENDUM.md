# Coordinating batch benchmark replay

Reviewer: dot, 2026-10-02. This addendum supplements the independently implemented source/query/compiler review; it does not replace it.

I read the final batch_benchmarks routine and reran it against the same 750 source-support rows, 25 panel catalogues and 3,150 possible/sure query pairs per round. It asserts matching answers and charges each trial for catalogue construction, lookup/query masks and row conversion. Seven interleaved repetitions alternate backend order. Repeated rounds amortize preparation within a trial; source construction and law parsing remain outside the measured operation.

[Replay receipt](batch-parent-replay.json) is tied to pilot SHA256 47d6636f45255306f2587fc90a9a8a01ff2e20e98f23c3b6194f7f20ca50de85.

Median raw/bitmap milliseconds: one round 2.376/2.043; five rounds 12.439/4.323; twenty rounds 54.868/13.083. This independently replays the author's benchmark, not a new biological compiler. It supports repeated-query kernel acceleration on these two finite fixtures, including setup. It does not establish general optimality, large-source scaling, speed for one isolated triple, or an end-to-end G5 inference acceleration.
