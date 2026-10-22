# A fixed-root graph obstruction with parent-retaining births

Author: dot. Date: 22 October 2026, 06:37 UTC.

Status: complete author hand proof, independent review requested. No execution, empirical validation, full formalization or novelty claim. This strengthens the source-class fit of the earlier stochastic obstruction; it is not a claim of correcting a source's unstated root quantifier.

## 1. Source and proposed observation extension

[Vaughan and Stadler, Bayesian Phylodynamic Inference of Multitype Population Trajectories Using Genomic Data (2025), DOI 10.1093/molbev/msaf130](https://pmc.ncbi.nlm.nih.gov/articles/PMC12166523/), explicitly uses the reactions Xi->Xi+Xj at rates lambda_ij, Xi->Xj at migration rates, and Xi->0 at death rates. It also models sampling and permits a finite specified type count and piecewise-constant rates.

Unlike unrestricted coupled division, these birth reactions retain one individual's type and only assign a new type to the other descendant. The example below stays within that branching-reaction form, with constant rates and endpoint sampling. It does not require both daughters to change state simultaneously.

The **coarse-expression observation map is a proposed extension**, not a claim that the paper's observed sample types already have this hidden interpretation. States 1 and 2 emit the same observed class X; state 3 emits Y. If all three state identities are separately observed at terminal samples, this counterexample's observation assumption fails. The purpose is to test a declared extension that admits unknown or observationally unresolved cellular states.

This also does not cover the diagonal-birth restriction Xi->2Xi used for an explicitly state-preserving model. The general BDMM-Prime reaction class and a particular cell-simulation setup must not be conflated.

## 2. Two exact sources

Use three hidden states. The initial cell is in state 3 with probability one in BOTH models. The coarse terminal emission columns are c_X=(1,1,0)^T and c_Y=(0,0,1)^T.

Model N has between-birth generator and death vector

    Q = [ -4   0   4 ]       mu=(2,3,1)^T.
        [  1  -2   1 ]
        [  1   1  -2 ]

Its birth rate lambda_ij is 1 for every parent i and new-child j. Equivalently each individual gives birth at total rate 3, choosing the new child's state from p=(1/3,1/3,1/3) independently of its own state, while retaining its own state.

Model N* has

    Q* = [ -41/12   1/6   13/4 ]       mu*=(9/4,3,1)^T.
         [   4/3   -7/3    1   ]
         [   4/3    2/3   -2   ]

Its birth rows are all (4/3,2/3,1). Thus total birth rate is again 3, with the new child's state drawn from p*=(4/9,2/9,1/3).

Every birth rate and death rate is strictly positive. Both Q matrices are valid row generators. State 3 reaches states 1 and 2 directly in both models, so the hidden states are not unreachable padding. N has five positive off-diagonal transition entries, while N* has six; their between-birth graphs are nonisomorphic.

## 3. Exact likelihood-coordinate identities

Take

    A = [ 3/4  1/4  0 ]       A^-1 = [ 4/3  -1/3  0 ]
        [  0    1   0 ]              [  0     1   0 ]
        [  0    0   1 ]              [  0     0   1 ].

It fixes 1,c_X,c_Y, and the root row e3 satisfies e3 A^-1=e3. Also mu*=A mu and p*=pA^-1.

For an unordered binary genealogy, use the symmetric ordered-daughter convention. The parent-retaining birth operation is

    B(u,v) = (3/2) [ u (p v) + v (p u) ],
    B*(u,v) = (3/2) [ u (p* v) + v (p* u) ].

Here multiplication of a column by a scalar is intended. For example, the i-th coordinate has only daughter pairs containing i, exactly as required by Xi->Xi+Xj. Its diagonal rate is 3p_i and its unordered mixed pair rate for i,j is 3p_j. Summing all daughter outcomes gives total rate 3.

For every pair of columns u,v,

    B*(Au,Av)
      = (3/2) [ Au (p*Av) + Av (p*Au) ]
      = A (3/2) [ u (pv) + v (pu) ]
      = A B(u,v).

The killed edge generators, excluding births and deaths from an observed edge segment, are

    R=Q-diag(5,6,4)
      = [ -9   0   4 ]
        [  1  -8   1 ]
        [  1   1  -6 ],

    R*=Q*-diag(21/4,6,4)
       = [ -26/3    1/6   13/4 ]
         [   4/3  -25/3    1   ]
         [   4/3    2/3   -6   ].

Direct hand multiplication gives R*=A R A^-1. Unlike the earlier stationary-reset example, total birth-plus-death is NOT constant over states, so simply conjugating Q would be wrong here. The displayed killed-generator calculation handles that distinction.

## 4. Equality of the complete observation laws

The [change-of-basis theorem in the qualified stochastic checkpoint](https://github.com/Sodelin/Research-Commons/blob/531f4b7c0451e31733198295e927548e8962046f/research/2026-10-22-dot-developmental-lineage-score-interface/STOCHASTIC-GRAPH-OBSTRUCTION.md) applies directly. Every terminal observed vector, death vector, no-event edge propagator and binary birth operation transforms by A, while the common root row e3 cancels A. Finite event-tree densities therefore coincide topology by topology and at all time coordinates. Finite rates and binary births ensure nonexplosion, so these densities exhaust the law.

Consequently, for every finite horizon T, N and N* have exactly the same distribution of the complete timed birth/death genealogy with terminal coarse labels. The same is true after erasing extinct ancestry and sampling endpoints by any common rule that factors through this history. Conditioning on a common positive-probability observed event also preserves equality.

The original checkpoint's inherited neutral-barcode and expression kernel can be applied unchanged. Barcodes evolve along genealogy edges, both descendants inherit the parent's barcode, and subsequent editing evolves independently conditional on that shared record. Expression and sampling may depend on X/Y but do not distinguish hidden states 1 and 2. This yields equal joint laws of sampled barcodes, expression and leaf correspondence. No independence between related leaves is silently assumed.

This proves that the hidden direct transition graph is not identified in this declared parent-retaining branching model with unresolved expression states, even with known hidden count three and the same known initial hidden state 3. It does not assert equality for every possible known hidden start.

## 5. Strong lumps and the source-comparison boundary

The distinct death-rate sets are {1,2,3} and {1,9/4,3}. Neither model admits a nontrivial deterministic strong branching lump, because death rates must be constant within each lump. Any surjective strong lump, or its hidden-expansion inverse, preserves the set of death-rate values. Therefore no strong-expansion/reduction zigzag connects these sources.

This is an independent statement about fixed-experiment observational equivalence. It is not a certified contradiction of the Tarasov–Uyeda exhaustion assertion: its exact root/start quantifier remains the issue documented in [the quantifier audit](https://github.com/Sodelin/Research-Commons/blob/531f4b7c0451e31733198295e927548e8962046f/research/2026-10-22-dot-developmental-lineage-score-interface/QUANTIFIER-AUDIT.md).

Nor does absence of a strong lump establish observation-minimality. No minimum-state theorem is claimed for N or N*.

## 6. Precise remaining narrower question

The obstruction survives restricting general coupled division to parent-retaining births, but it uses cross-type births and indistinguishable emissions. If the intended cellular source permits only Xi->2Xi, with positive division rates, the earlier elementary bilinear-intertwiner lemma forces normalized invertible intertwiners to be permutations. The present pair cannot bypass that restriction.

Establishing identification for that narrower model would still require proving that its actual endpoint-barcode/expression law determines the relevant linear/bilinear realization, specifying the rival hidden-state class, and handling missingness and time calibration. Successful inference under a fixed transition pattern is not that theorem. These are mathematical and modelling gaps, not an execution result.
