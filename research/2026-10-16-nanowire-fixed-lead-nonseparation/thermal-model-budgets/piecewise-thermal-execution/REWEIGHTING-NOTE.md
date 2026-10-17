# Thermal-mass reweighting of the saved cells

2026-10-17 19:09 UTC. dot (OpenAI), with Nolan. Coordinating calculation, pending independent review of the complete cell certificates and this integration.

The 60 previously computed energy-cell conductance enclosures were reused unchanged. No matrix inverse was recomputed. Both scripts verify contiguous coverage of the saved domain and witness hashes. They are conditional on validity of the original cell enclosures; hash equality alone does not prove those enclosures.

First, a positive 24-term cosh series lower bound bounds the Fermi kernel above at the smallest absolute energy in each cell. This gives warm conductance upper approximately 0.5321965904031198 and Q lower approximately -0.07015249466297067.

Second, integrate_cell_masses.py encloses the logistic cumulative distribution at each cell endpoint. For v=abs(x)/theta, s=sum(j=0..60)v^j/j! is a lower bound for exp(v). The remaining positive tail is at most (v^61/61!)/(1-v/62), because v<62 and each subsequent term ratio is at most v/62. The resulting rational exponential interval is mapped monotonically into the logistic function. Subtract the lower CDF bound at the left endpoint from the upper bound at the right endpoint to upper-bound cell mass. Multiply by the cell's nonnegative conductance upper bound and round upward to denominator10^18. Retain the previous rigorous exterior-tail bound.

At the unchanged T=1mK, error eta=.001, zero drift, this gives warm upper approximately 0.5175952886251786 and Q lower approximately -0.04094989110708811. The bound remains INCONCLUSIVE. This negative lower bound does not imply a negative determinant or a failed physical device. The sufficient all-allowed-reports criterion requires warm upper below (1-f0_upper-2eta)/2, which is not met. No practical certificate or historical novelty is claimed.

The original uniform-kernel run and both sharpenings are retained. A possible next step is refining cells responsible for the largest thermal upper-bound contributions, with fresh validated local enclosures only where needed. No such refinement was run in this note.
