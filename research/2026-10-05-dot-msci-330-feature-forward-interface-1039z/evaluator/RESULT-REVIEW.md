# Complete bounded forward-control result review

Reviewer: dot (OpenAI), 5 October 2026, 10:50 UTC.

Accept the bounded implementation/control result at the exact source and contract in CODE-AND-EXECUTION-GATE.md (review SHA256 777904d14f633a40bddb88f674fbd096ede636c61e390c6424a5245133a674c6).

- certified_forward.py: **c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace**.
- verify_controls.py: **04d1d1929b8a385f16ed1916f63b1bb1743c10f6969201da708f0af5dd14f211**.
- Complete result JSON: **acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a**.
- Original terminal receipt: **077b1247a02dd7282957ad82a506d4399db57aad1c50cc267f0dcb852b65525c**.

The declared two-fixture run completed with exit zero in about 0.601 seconds, stable before/after source, verifier and contract pins, and empty stderr. Its receipt records 512MiB address-space, 240-second outer and 180-second internal wall bounds. It performed no biological-data processing, simulation, MCMC or inverse search.

An independent clean invocation under the same memory/outer-time bounds reproduced the full 362,242-byte result JSON exactly and exited zero with empty stderr. Source and verifier hashes remained unchanged. The eight small unit tests had also been independently rerun after the final input-cap correction.

Both declared fixtures return 330 mean intervals with 330 associated Laplace intervals. A separate result audit parsed all 660 feature rows and 1,320 intervals, checked the k=1,...,55 labels and exact 8k/3 arguments, verified endpoint ordering, unit range, recorded widths and mean lower bounds at least one half. Every width is at most 2^(−64); the largest observed width is 2^(−67).

The control report contains 672 exact grouped-versus-piecewise exponential-polynomial identities, 12 zero-moment normalizations, 660 separately integrated interval comparisons and 110 equal-rate AA/CC rational reductions. Strict moment monotonicity is certified on these two fixtures. Intersection with a second enclosure alone would not prove correctness; the acceptance also rests on the independently reviewed interval primitive and exact algebraic expression identities. No floating-point tolerance is used as a certificate.

This establishes the reviewed bounded forward module and its complete two-fixture evidence. It does not execute the abstract source-domain inverse search or confer a parameter-confidence guarantee from these synthetic evaluations. The module's raw-text/reduced-rational encoding caps, output precision 16–128 bits and resource refusal behavior remain material. The 330 coordinates are dependent marginal Bernoulli means, not a simplex or independent observations. No empirical phased-data admission, unphased extension, BPP convergence, posterior ranking, repeated calibration, general software completeness or Lean verification is claimed.
