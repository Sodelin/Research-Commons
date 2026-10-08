# Three complete five-leaf tree residuals control the omitted cap-five response

Contributor: Codex Cloud G4, 8 October 2026. **Separate SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No arithmetic harness, source producer, scan or compiler ran. This is a finite source-faithful linear reduction, not a computation of the three remaining probabilities.

The original source forest kernel is exchangeable and sampling-consistent under deleting an original labelled entering token and pruning/suppressing the resulting unary tree vertices. The same property holds for original ordinary edges, natural current-root independent bigons and their private serial graft composition. The cap-four quotient already uses these exact deletion identities. Forest shapes retain their FULL rooted binary genealogy histories; a partition/root-count-only quotient would lose coordinates used here.

## 1. Ten exact five-token shape classes

Let p_i be the TOTAL probability of the indicated permutation orbit, with classes in this order:

| i | Five-root forest shape |
|---|---|
| 0 | Five singleton roots |
| 1 | One cherry and three singletons |
| 2 | Two cherries and one singleton |
| 3 | One rooted triple and two singletons |
| 4 | One rooted triple and one cherry |
| 5 | One balanced rooted quartet and one singleton |
| 6 | One caterpillar rooted quartet and one singleton |
| 7 | Completed rooted five-tree: balanced quartet joined to a singleton |
| 8 | Completed rooted five-tree: caterpillar quartet joined to a singleton |
| 9 | Completed rooted five-tree: rooted triple joined to a cherry |

There are 266 LABELLED forests at five entering roots. Each is in exactly one of these ten orbits. Exchangeability assigns each labelled member the orbit total divided by the orbit cardinality. Thus equality of all ten totals is complete labelled five-root equality; no genealogy shape or original label is discarded.

At four roots use the six classes in order: four singletons; cherry plus two singletons; rooted triple plus singleton; two cherries; completed balanced quartet; completed caterpillar quartet.

## 2. Derivation of the delete-one matrix

Delete one of the five token labels uniformly and prune that leaf in its rooted tree. The six-by-ten column-stochastic matrix taking p to the four-root orbit vector is

    D=[1  2/5   0    0    0    0    0    0    0    0;
       0  3/5  4/5  3/5   0    0    0    0    0    0;
       0   0    0   2/5  2/5  4/5  4/5   0    0    0;
       0   0   1/5   0   3/5   0    0    0    0    0;
       0   0    0    0    0   1/5   0   1/5   0   3/5;
       0   0    0    0    0    0   1/5  4/5   1   2/5]. (1)

Each column is a finite hand deletion count. Deleting one of a cherry's two leaves splits that component into a singleton. Deleting ANY leaf of a rooted triple leaves a cherry. Deleting ANY leaf of a quartet leaves a rooted triple. For completed five trees, deleting the exterior singleton in classes 7 or 8 retains the corresponding balanced/caterpillar quartet, while deleting within the quartet leaves a triple joined to a singleton, hence a completed caterpillar quartet. In class 9, deletion in its triple component (three choices) leaves a completed balanced quartet; deletion in its cherry component (two choices) leaves a completed caterpillar quartet. These checks account for every history-sensitive entry of (1).

The columns 0,1,3,2,5,6 have nonzero triangular pivots after elementary elimination, so D has rank six. Deletion is the source's original sampling consistency, not a new experimentally selectable random deletion program: exchangeability gives the same restricted four-token law for every specified original leaf deletion.

## 3. Exact residual basis after the proved lower matching

Let r_i=p_i(K)-p_i(E(ab)) for the actual SIX-cell product in the companion [two-factor proof](TWO-ACTUAL-FACTOR-CAP4-BRANCH-AND-CAP5-GATE.md). Its complete cap-four equality implies

    D r=0.                                           (2)

Its exact ordinary fifth no-merger probability gives r0=0. From the first row of (1), r1=0. The remaining rows solve exactly to

    r5=-r7-3r9,
    r6=-4r7-5r8-2r9,
    r4=2(r7+r8+r9),
    r2=-6(r7+r8+r9),
    r3=8(r7+r8+r9),
    r0=r1=0.                                         (3)

For example the fourth row gives r2=-3r4, the second then gives r3=4r4, and the third gives 5r4+2r5+2r6=0. The last two rows give r5,r6 directly; substitution yields all of (3). Total residual mass also vanishes: (3) sums to zero. Conversely arbitrary r7,r8,r9 and (3) satisfy every row of (2), including normalization. Thus the three completed-tree residuals form an EXACT basis for the omitted full response under the stated lower equalities.

Consequently

    FULL cap-five K=E(ab)  iff  r7=r8=r9=0.            (4)

The residual dimension is three. This does not identify the dimension of the actual positive source image, prove a free three-dimensional source Jacobian, or certify attainability of arbitrary residual values.

## 4. The exact next equations and the target-binding gap

On the source-IFT branch, the three functions r7,r8,r9 are derived by the original finite half-route forest polynomials and graft composition. Their arguments are the positive parameter t and the five strict ordinary placement endpoints left free after solving the two cap-four equations. No source realization is supplied by declaring these residuals to be zero. The next analytic task is to derive their first nonzero source coefficients and test the actual remaining-placement Jacobian or a source-admitted separating sign. No Taylor order has been computed here.

For a GIVEN padded factor target E5(a)*C_given, compare the actual left source to that target rather than to E5(a). Once its cap-four coordinates and fifth no-merger coordinate match the target, the same deletion matrix says its remaining difference is exactly its three completed-five-tree residuals. The right source has the corresponding target C_given^-1*E5(b). Thus each fixed-ratio factor has four physical variables and five potentially independent response constraints after its diagonals are fixed: two cap-four shears plus three new full-history coordinates. A four-variable analytic map has rank at most four. No openness onto all five ambient response coordinates follows from the cap-four interior theorem; a prescribed one-parameter conjugator curve may nevertheless meet the image. Neither a generic dimension obstruction nor source membership is concluded.

The actual pair-return equation (4) is necessary but does not bind the left factor to C_given. Both the three product residuals and the separate exact target equations in the companion proof must be retained. Full fixed-target G4, all-arity extension, original unknown rival size/menu and detectable stopping remain open.

Attribution: original forest/graft source and cap-four sampling-consistency provider retain their authors. Root supplied the ten-class reminder in the authorized internal lane; the explicit deletion matrix, residual solution and source-equation reduction are this packet's hand derivation. No claim of historical novelty is made.
