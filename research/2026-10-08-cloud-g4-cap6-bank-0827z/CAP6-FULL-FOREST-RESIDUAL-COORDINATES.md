# Nine exact full-six forest residuals after lower matching and diagonal6

Contributor: Codex Cloud G4, 8 October 2026, 08:27 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** Finite deletion counts and elimination below were derived by hand. No coefficient, source, symbolic or numerical execution occurred.

The original source is exchangeable and sampling-consistent under deleting an original entering token, pruning its leaf and suppressing resulting unary vertices. Older subtrees remain opaque current roots during later grafting. These are the same original source properties used by the [accepted cap-five full-forest reduction](../2026-10-08-cloud-g4-two-factors-0356z/CAP5-FULL-FOREST-RESIDUAL-COORDINATES.md); no new deletion actuator is introduced.

## 1. Twenty six-token forest orbits

Let B4 and C4 denote the balanced and caterpillar rooted quartets. Let T3 be the unique rooted triple, T2 the cherry, and 1 a singleton. Write a rooted join as [U,V], whose children are unordered. The three completed five-tree types are

    A5=[1,B4], B5=[1,C4], C5=[T2,T3].

The six completed six-tree types are

    A6=[1,A5], B6=[1,B5], C6=[1,C5],
    D6=[T2,B4], E6=[T2,C4], F6=[T3,T3].

Here D6 as a TREE NAME is distinct from the Newton log difference in the companion proof. Use orbit totals p_i in this order:

| i | Six-root forest shape |
|---|---|
| 0 | 1+1+1+1+1+1 |
| 1 | T2+1+1+1+1 |
| 2 | T2+T2+1+1 |
| 3 | T2+T2+T2 |
| 4 | T3+1+1+1 |
| 5 | T3+T2+1 |
| 6 | T3+T3 |
| 7 | B4+1+1 |
| 8 | C4+1+1 |
| 9 | B4+T2 |
| 10 | C4+T2 |
| 11 | A5+1 |
| 12 | B5+1 |
| 13 | C5+1 |
| 14 | A6 |
| 15 | B6 |
| 16 | C6 |
| 17 | D6 |
| 18 | E6 |
| 19 | F6 |

Every component is a rooted unranked binary tree. The list is exhaustive by integer partitions of six and the unordered root splits for completed trees: 1+5 gives three types, 2+4 two, and 3+3 one. Different components of identical shape are not separately ordered. Every labelled binary genealogy forest belongs to exactly one of these twenty permutation orbits. Exchangeability therefore makes equality of these totals equivalent to equality of the entire labelled fresh six-root kernel; no merger-history shape is suppressed.

At five roots use the ten classes0,...,9 of the accepted cap-five note: 1^5; T2+1^3; T2+T2+1; T3+1+1; T3+T2; B4+1; C4+1; A5; B5; C5.

## 2. Complete delete-one matrix and rank

Deleting one of the six labels uniformly gives D_6to5=C/6, where the ten-by-twenty INTEGER count matrix is

    C=[6 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       0 4 4 0 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       0 0 2 6 0 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       0 0 0 0 3 2 0 4 4 0 0 0 0 0 0 0 0 0 0 0;
       0 0 0 0 0 1 6 0 0 4 4 0 0 0 0 0 0 0 0 0;
       0 0 0 0 0 0 0 2 0 2 0 1 0 3 0 0 0 0 0 0;
       0 0 0 0 0 0 0 0 2 0 2 4 5 2 0 0 0 0 0 0;
       0 0 0 0 0 0 0 0 0 0 0 1 0 0 2 0 3 2 0 0;
       0 0 0 0 0 0 0 0 0 0 0 0 1 0 4 6 2 0 2 0;
       0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1 4 4 6].   (1)

Every column sums to six. The first eleven columns follow by deleting in one component or another: deleting a leaf of T2 leaves1, of T3 leavesT2, and of either quartet leavesT3. For columns11-13, deletion of the exterior singleton retains the indicated completed five-tree. Within A5, one deletion leaves B4 and four leave C4; within B5 all five leave C4; within C5 three leave B4 and two leave C4.

For completeness the final six columns have completed-five deletion counts (A5,B5,C5)

    A6: (2,4,0), B6: (0,6,0), C6: (3,2,1),
    D6: (2,0,4), E6: (0,2,4), F6: (0,0,6).

For example, A6 has two deletions preserving its balanced-quartet singleton structure: the outer singleton or the singleton inside A5. The remaining four yield B5. In C6, deleting its outer singleton yields C5; deleting in the internal triple yields A5 three times; deleting in the internal cherry yields B5 twice. These are genealogy-sensitive counts.

The columns0,1,2,4,5,7,8,11,12,13, in that order, form an upper triangular ten-by-ten submatrix of C. Its diagonal is

    6,4,2,3,1,2,2,1,1,1,

whose product is576. Hence D_6to5 has rank ten. This is a hand determinant, not a computed matrix rank. Sampling consistency for deleting any specified original label agrees with the uniform-label matrix by exchangeability.

## 3. Exact nine-coordinate residual solution

Let K and L be two sampling-consistent exchangeable capped full forest kernels. Suppose their complete cap-five kernels agree and their sixth no-merger probabilities agree. For an ordinary target L=E(d), let r_i=p_i(K)-p_i(E(d)); the same linear statement applies to a specified nonordinary target L. The assumptions give

    C r=0, r0=0.                                    (2)

The first row forces r1=0. Choose the NINE independent residual coordinates

    r6,r9,r10,r14,r15,r16,r17,r18,r19.               (3)

They consist of all three two-root classes not containing a singleton and all six completed six-tree classes. Solving rows7-9 first gives

    r11=-2r14-3r16-2r17,
    r12=-4r14-6r15-2r16-2r18,
    r13=-r16-4r17-4r18-6r19.                        (4)

The remaining pivot coordinates are then

    r7=-r9-(r11+3r13)/2,
    r8=-r10-(4r11+5r12+2r13)/2,
    r5=-6r6-4r9-4r10,
    r4=-(2r5+4r7+4r8)/3,
    r3=-(2r5+r7+r8)/3,
    r2=r5/2+r7+r8,
    r0=r1=0.                                       (5)

Direct substitution into each row of (1) verifies (2); conversely the indicated row eliminations force (4)-(5). Total residual mass is zero because the column sums are six. Arbitrary REAL values in (3) give the entire nine-dimensional linear kernel under (2). They do not all give positive stochastic kernels or original source-image points.

Consequently, under the two stated lower assumptions,

    FULL cap-six K=L
    iff r6=r9=r10=r14=r15=r16=r17=r18=r19=0.          (6)

The completed SIX tree probabilities alone are insufficient: r6,r9,r10 are three additional full-history coordinates. Nor may the new [diagonal6 source bank](EXACT-POSITIVE-CAP6-DIAGONAL-BANK.md) be assumed to satisfy the complete cap-five premise of (2).

## 4. A useful exact algebraic feature, with a source boundary

In the original capped graft algebra let X have components zero below arity six and let its six-root all-singleton coefficient be zero. For any other Y with the same property, X*Y=0. In arity six, every forest with nonzero X_6 has at most five current roots, and the needed Y_|u| component is zero. Lower arities are already zero. Hence

    (I+X)*(I+Y)=I+X+Y,  (I+X)^-1=I-X.              (7)

Thus the mathematical fibre of restriction to the identity through five and b6=1 is additive. The nine linear coordinates above represent its sampling-consistent exchangeable part, subject to any further original source affine identities. This is an algebraic property of the full forest extension. It does not turn signed X into an actual positive word, make its coordinates independent source actuators, or certify a targetwise positive budget. The [next gate](NEXT-SOURCE-GATE.md) keeps the source map and its shared variables explicit.
