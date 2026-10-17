# Candidate same-device 1 mK thermal certificate

2026-10-17 19:15 UTC. dot (OpenAI), with Nolan. Independent review pending. No Lean verification, experimental validation, general device-identification result, or historical-novelty claim.

Starting from the previously saved 60-cell enclosure, rank cells by the upper contributions in piecewise-thermal-execution/CDF-RESULT.json. Split the four largest once. Exactly eight new local inverse proposals were checked by exact Gaussian-integer residual arithmetic; the other 56 cells and their witnesses were reused. The result covers the same complete energy domain with 64 cells. No physical parameter or temperature changed.

The original uniform-kernel integration still fails (warm upper about0.7370). Integrating certified rational bounds for the actual Fermi probability mass of each cell gives warm conductance upper about0.46749492079652594 and determinant lower about0.05925084455021722, at T=1mK, deterministic readout error eta=.001, zero drift, for the unchanged positive 60-site mathematical control at B=2meV.

The calculation uses the saved f0 bound and a deliberately conservative same-device thermal error bound fT+f0. The all-allowed-reports criterion is Q>=1-2warm_upper-f0_upper-2eta. This checks that a known model admits a sufficient thermal measurement budget. It does not show unknown experimental devices satisfy the model, infer arbitrary device parameters, or obtain a universal bound from a measured conductance alone.

Reproduce with certify_piecewise.py, then integrate_cell_masses.py. Dependencies: sibling piecewise-thermal-execution and thermal-budget-execution. Prior failures remain preserved. RESULT.json contains the cell data; CDF-RESULT.json contains exact rational integrated bounds. New witnesses are local; reused witnesses have explicit relative paths to the original directory. Review must check every reused and new cell certificate, the partition, physical reconstruction, thermal tail, rounding, and target inference before accepting the positive candidate.
