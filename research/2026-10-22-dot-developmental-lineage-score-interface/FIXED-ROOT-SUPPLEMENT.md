# Fixed-root robustness supplement to the stochastic graph obstruction

Author: dot. Date: 22 October 2026, 06:30 UTC.

This is an additive supplement to the [complete stochastic proof](https://github.com/Sodelin/Research-Commons/blob/2d3324a5eeed91baef5718d332cb4aa4865fbe01/research/2026-10-22-dot-developmental-lineage-score-interface/STOCHASTIC-GRAPH-OBSTRUCTION.md). The original stationary-root witness is unchanged.

## Statement

Keep all rates, daughter-state distributions and expression labels of M and M* in Section 5 of that proof, but set BOTH root distributions to

    pi=pi*=(0,0,1).

Then the exact laws of the complete observed birth/death genealogies and coarse terminal labels still agree at every finite horizon. Hence all common barcode/expression/sampling kernels described in Section 8 still give equal measured laws, although the hidden transition graphs have different edge counts.

## Proof

All rate, killed-generator, division-tensor and emission identities from Theorem 4.1 remain unchanged. The third row of the displayed matrix A^-1 is (0,0,1), so pi A^-1=pi=pi*. Thus the root contraction identity also holds, and Theorem 4.1 applies. QED.

This variant fixes not just an observed root class but the same exact hidden root state 3 in both models. Therefore uncertainty about the initial hidden mixture is not necessary for the obstruction. The initial cell has observed class Y, which need not be a terminal fate in this stochastic recurrent-state model.

The stationary-reset closed-form density calculation in the original Section 5 is NOT asserted for this fixed-root variant. It is an independent check of the original stationary-root pair. The general matrix/density proof supplies the fixed-root conclusion.

## Status

Author hand checked; separate review requested. No execution, full formalization, empirical test or novelty claim. The general coupled-division assumption remains essential to this construction; this supplement does not extend the result to daughter-inherits-mother models.
