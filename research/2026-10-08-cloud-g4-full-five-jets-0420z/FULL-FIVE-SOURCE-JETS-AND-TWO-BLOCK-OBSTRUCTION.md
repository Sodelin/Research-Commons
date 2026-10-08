# The first full five-root jet blocks the strict two-block return branch

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 04:20 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** Every coefficient below is derived by hand from the preserved original source. No deterministic symbolic exploration, arithmetic harness, source producer, parameter scan, numerical solver, compiler, Actions or API ran.

The [two-factor packet](../2026-10-08-cloud-g4-two-factors-0356z/README.md) constructs two actual strict three-cell words at fixed a,b, with exact full cap-four inverse response and ordinary diagonals through five. It leaves three complete rooted-five-tree residuals. This note derives their exact finite-source formulas and explicit THIRD-order jets. Their joint coefficient cannot vanish at any fixed strict placement/comparable scale. Thus the constructed branch cannot be lifted to full cap five by adjusting its remaining interior placements. Degenerating placements/scales, other source architectures and the GIVEN conjugator problem remain separate.

## 1. Actual finite forest matrices, not a count-only quotient

Use the ten FULL five-token forest shape classes 0,...,9 of the [complete deletion reduction](../2026-10-08-cloud-g4-two-factors-0356z/CAP5-FULL-FOREST-RESIDUAL-COORDINATES.md): singletons; cherry+three singletons; two cherries+singleton; triple+two singletons; triple+cherry; balanced quartet+singleton; caterpillar quartet+singleton; completed balanced-quartet-plus-singleton tree; completed caterpillar-quartet-plus-singleton tree; completed triple-plus-cherry tree. Their labelled orbit sizes are

    (1,10,15,30,30,15,60,15,60,30), total 266.          (1)

Current components retain their complete genealogy histories. Original exchangeability makes this an exact orbit aggregation; each labelled coordinate is recovered by dividing its orbit total by (1). Graft transitions distinguish balanced/caterpillar histories throughout.

The actual ordinary pair-merger generator Q, in these classes, has the following nonzero rows. An entry j:v means transition to class j at rate v; every omitted entry is zero.

| row | diagonal | off-diagonal entries |
|---|---:|---|
| 0 | -10 | 1:10 |
| 1 | -6 | 2:3, 3:3 |
| 2 | -3 | 4:2, 5:1 |
| 3 | -3 | 4:1, 6:2 |
| 4 | -1 | 9:1 |
| 5 | -1 | 7:1 |
| 6 | -1 | 8:1 |
| 7,8,9 | 0 | none |

These are counts of actual current-root pairs. For example the two cherries in class 2 can join each other to form a balanced quartet, or either can join the singleton to form a triple+cherry. They are not interchangeable with class 3's triple+two-singleton mergers. The ordinary matrix is E(z)=exp[-log(z)Q], whose coordinates are the original rational polynomials in survival z.

For an actual half-coin bigon B(x,y), its exact orbit matrix is the original CURRENT-root routing sum: at a representative forest of class i with n current roots, sum all subsets S of those roots with weight 2^-n; apply the ordinary kernel E(x) to S and E(y) to its complement, retain all generated subtrees, and graft their union into the original forest. Sum the results over output class j. This FINITE formula defines B_ij(x,y) as a rational polynomial. It uses roots of prior trees as opaque tokens, not each descendant leaf.

Consequently the exact three residual functions on the ACTUAL branch are the finite polynomials/analytic compositions

    r_j(t;theta)= [e0 K_P(t;theta) K_R(t;theta)]_j
                      -g_j A5(ab),      j=7,8,9,     (2)

where each K is the actual product E(zeta)B1E(z1)B2E(z2)B3E(u) with the preserved source-IFT weights and strict fixed-pair calibration. e0 is the all-singleton row, g=(1/6,1/3,1/2), and

    A5(z)=1-2z+(10/7)z^3-(1/2)z^6+(1/14)z^10.        (3)

The g values follow from the ordinary embedded pair-merger chain on these full shapes. Formula (2), with the finite route/graft sum above, specifies the exact source functions at EVERY positive t on the branch; no prescribed signed moment is substituted as a source law. Full higher-order polynomial expansion is unnecessary for the obstruction below and has not been executed.

## 2. Derive the leading bigon forest operator from the original source

For a cell labelled A=1,6,10 set s=1-At, h^2=w(t)t^3, x=s-h,y=s+h and q=(1+s)/2. The accepted diagonal/quotient formulas give

    gamma=A^3/12-w(0)/2,
    B(x,y)-E(q)=gamma t^3 R+O(t^4)                   (4)

through cap FIVE. Here R is derived as follows, rather than assumed from its diagonals.

At cap four the original exact source gives third-order difference orbit vector

    (-6,9,-3,0,0,0) gamma

in the six complete classes. This follows from b3-q^3=-(3/2)gamma t^3+O(t^4), b4-q^6=-6gamma t^3+O(t^4), C=gamma t^3+O(t^4), H=0, and the preserved sampling/forest reconstruction identities. At cap three the analogous vector is (-3/2,9/4,-3/4)gamma; cap two difference is zero.

The five-root diagonal difference is -15gamma t^3+O(t^4), because its third log defect is 10 times the three-root defect at this order. Every completed five-tree probability of BOTH B and E(q) is O(t^4): completing five initial roots requires four binary mergers, and each physical arm loss is O(t). Thus all THREE completed five-tree THIRD coefficients are zero. Solve the preserved exact six-by-ten delete-one matrix using this diagonal, the complete four-root vector and those three zeros. The UNIQUE result is

    (-15,45/2,0,-15/2,0,0,0,0,0,0) gamma.             (5)

No five-root history coefficient has been fitted independently. Exchangeability distributes (5) over labelled forests, and original token grafting extends it to prebuilt current trees. On n current roots, R therefore has

    all-singleton coefficient -(3/2)binom(n,3),
    EACH pair-merger coefficient (3/4)(n-2),
    EACH rooted triple-merger coefficient -1/4,
    every other fresh forest coefficient zero.       (6)

A rooted triple merger has one of the three labelled cherry-first histories. Formula (6) is the actual finite forest jet, not a probability kernel or an admitted signed generator.

Its full ten-class graft matrix is

| row | diagonal | off-diagonal entries of R |
|---|---:|---|
| 0 | -15 | 1:45/2, 3:-15/2 |
| 1 | -6 | 2:9/2, 3:9/2, 4:-3/4, 5:-3/4, 6:-3/2 |
| 2 | -3/2 | 4:3/2, 5:3/4, 7:-1/4, 9:-1/2 |
| 3 | -3/2 | 4:3/4, 6:3/2, 8:-1/2, 9:-1/4 |
| 4,5,6,7,8,9 | 0 | none |

For example class 1 has one cherry and three singleton roots. A triple of singleton roots gives triple+cherry; a triple containing the existing cherry and two singletons gives a balanced quartet if those singleton roots merge first, and a caterpillar quartet in the other two rooted histories. This explains its three negative triple entries. Every row sums to zero. Symmetric original routing polynomials and bounded positive w give uniform finite O(t^4) remainders locally on the source branch.

## 3. Exact ordinary transport of this full-shape jet

Let X be the inverse of the ordinary survival downstream from a primitive insertion. Algebraically its unit-diagonal-normalized transport is

    R_X=E(X)R E(X^-1).                                (7)

X>1 is AUXILIARY algebraic normalization, never an admitted negative-duration edge. All original word factors remain strictly positive. Compute the completed five-tree entries f_j(X)=[e0 R_X]_j from the two displayed FULL-shape matrices. The hand result is

    f7=(15/8)X^10-(5/2)X^9+(15/28)X^7
                         -(5/8)X^6+(3/4)X^5-1/28,
    f8=-(5/4)X^10+(5/2)X^9-(10/7)X^7
                         -(5/4)X^6+(3/2)X^5-1/14,
    f9=-(5/8)X^10+(5/14)X^7
                         +(15/8)X^6-(3/2)X^5-3/28.  (8)

Here is a finite reproduction of those coefficients. Write z=1/X and let A_n(z) be the ordinary complete-to-one probability:

    A2=1-z,
    A3=1-(3/2)z+(1/2)z^3,
    A4=1-(9/5)z+z^3-(1/5)z^6,
    A5 given by (3).

The prefix probabilities at four and three roots are

    P54(X)=(5/2)(X^6-X^10),
    P53(X)=(20/7)X^3-5X^6+(15/7)X^10.                (9)

Conditional on prefix root counts, states 2,3 have equal probability P53/2. Their ordinary completion shape vectors are (1/3,0,2/3) and (0,2/3,1/3); states 0,1 have g=(1/6,1/3,1/2). Inserting the exact R table gives

    K=X^10[-15A5(z)+(45/2)A4(z)]
          +P54(X)[-6A4(z)+9A3(z)]
          +P53(X)[-(3/2)A3(z)+(9/4)A2(z)-3/4],
    K=-(15/4)X^9+(45/14)X^7+(15/2)X^6
                                      -(27/4)X^5-3/14,
    G=X^10 A3(z)=X^10-(3/2)X^9+(1/2)X^7,
    H=P54(X)A2(z)=(5/2)(X^6-X^5-X^10+X^9),
    f7=K/6-(3/4)H,
    f8=K/3-5G-(3/2)H,
    f9=K/2-(5/2)G-(3/4)H.                            (10)

Equations (9),(10) expand directly to (8). Triple histories are essential: the R row from two-cherries+singleton reaches class 7 or 9, while that from triple+two-singletons reaches class 8 or 9. A count-only operator would lose precisely these contributions. No coefficient script was run.

## 4. The first jets of the actual two-factor return branch

Use the exact source branch with t_P=t, t_R=rho(t)^(1/3)t and rho(t)->rho0>0. Let X_P1>X_P2>X_P3>1 and X_R1>X_R2>X_R3>1 be the strict limiting downstream inverse survivals. They satisfy X_P1<1/a and X_R1<1/b. Original label-attached coefficients are

    gamma_1=-577/150,
    gamma_6=-240881/4800,
    gamma_10=51869/960,
    gamma_1+gamma_6+gamma_10=0.                       (11)

In the unit normalization of the WHOLE product, the six support positions and weights are

    Z_Pi=X_Pi/b,        weight gamma_sigmaP_i,
    Z_Ri=X_Ri,          weight rho0 gamma_sigmaR_i.    (12)

All six supports are distinct: the first block lies strictly above 1/b, and the later block strictly below 1/b. This transport by the SAME fixed b is derived by ordinary conjugation of the first block across the second block's zeroth-order E(b), not selected by arity.

Define their signed moments M_k=sum weights*Z^k. Individual blocks have zero leading mass, so M0=0. Exact cap-four inverse matching forces M5=M6=0, by the preserved full quotient derivation. Expanding the actual graft product with (4),(7) gives its leading unit-normalized full-shape perturbation sum weights R_Z. Cross terms between two third-order insertions begin at t^6; source corrections and the solved placement/rho changes affect O(t^4), not the THIRD coefficient.

Because the lower four-root kernel is EXACTLY ordinary on the source branch, left multiplication by E(ab) contributes to its omitted five-root residual only through the all-five-singleton entry (ab)^10. Thus the EXACT functions (2) have jets

    (r7,r8,r9)^T
      =(ab)^10 t^3 L (M7,M9,M10)^T+O(t^4),           (13)
    L=[15/28   -5/2   15/8;
       -10/7    5/2   -5/4;
        5/14      0   -5/8],
    det L=375/448 !=0.                               (14)

All f_j terms at powers 0,5,6 disappear by M0=M5=M6=0. For a hand determinant check, 56L has rows (30,-140,105),(-80,140,-70),(20,0,-35), with determinant 147000; division by 56^3 gives (14). The vector first jet is fully specified; an individual component may have zero third coefficient at special placements, but the next section proves the THREE-component coefficient cannot be zero anywhere in this strict regime.

## 5. Five moment conditions cannot be cancelled by these source weights

If all three completed-five jets vanished, invertibility of L would give

    M5=M6=M7=M9=M10=0.                               (15)

The six actual support weights have FOUR negatives and TWO positives, all nonzero. Any ordering of those six weights therefore has at most four sign changes. This holds for every chronological permutation of each block, not only the two orders chosen in the branch.

Here is an explicit sign-separator proof that (15) is impossible. Order the positive support positions increasingly. If the weights change sign m times, choose one positive root r_j in each intervening gap. Orient a polynomial so its sign agrees with the weights. For m=0,1,2 use

    x^5 product_j(x-r_j),

which lies in span{x^5,x^6,x^7}. For m=3 use

    x^5 product_(j=1)^3(x-r_j)(x+sum_j r_j).

The inner x^3 coefficient vanishes, so this polynomial belongs to span{x^5,x^6,x^7,x^9}. Its extra root is negative and adds no positive sign change. For m=4 put s1=sum r_j>0 and s2=sum_(i<j)r_i r_j>0, and use

    x^5 product_(j=1)^4(x-r_j)(x+s2/s1).

The inner x^3 coefficient is s2-(s2/s1)s1=0; it belongs to span{x^5,x^6,x^7,x^9,x^10}. Again its extra root is negative. In every case, roots lie strictly in gaps, so the polynomial can be oriented to have the SAME nonzero sign as each support weight. The weighted sum of its values is then strictly positive. But (15) makes that sum zero, a contradiction.

This is a finite Chebyshev-moment obstruction derived from the actual full-shape source jet. It does not assume that an arbitrary signed gamma measure is source-realizable; the only measure used is forced by the six actual cells, strict original placements and comparable source scales.

## 6. Exact conclusion and the necessary escape

For every fixed strict endpoint/second-placement tuple in the genuine source-IFT branch, (M7,M9,M10) is nonzero. Therefore its THREE-component full five-root residual has first nonzero joint order t^3. It cannot equal zero for all sufficiently small positive t, and indeed at least one original completed-tree probability disagrees with E(ab) for each sufficiently small t. No adjustment within a fixed compact strict-placement/comparable-scale neighborhood can cancel all three; continuity and the positive moment-separation margin make the obstruction uniform on such a compact set.

The same leading argument excludes ANY two such 1:6:10 blocks with strict limiting ordinary placements and a finite positive limiting t_R^3/t_P^3, if they match cap four and seek full cap-five equality. Consequently neither the constructed branch nor an interior permutation/placement adjustment supplies the required pair-return prerequisite for cap-five factor membership.

This does NOT rule out paths whose ordinary placements coalesce as t->0, relative scales degenerate, leading positive/negative atoms cancel at coincident positions, other mean-ratio families, other coins, more cells or different original architectures. The omitted higher jets become controlling in those degenerate regimes. A negative or zero target shear is not separately declared globally impossible. Agreement with the GIVEN C_epsilon of the SAME middle source remains an additional equation even if another route supplies a product return.

The next genuine source task is a degenerate-placement or additional-cell architecture with a source-derived higher jet, rather than another search inside the now-excluded strict interior branch. All root/current-token/shared-parameter/copy-menu and fixed q,r constraints remain. Complete five-shape totals recover every labelled row by exchangeability and the preserved deletion identities; their discrepancies are actual authorized topology diagnostics via the original private tomography, not hidden forest readouts. Original fixed-target/full-prefix unknown-size G4 and detectable stopping remain OPEN. No compiler theorem or historical novelty claim is made.

Attribution: original current-root routing, complete forest algebra, ordinary source and tomography retain their contributors. The earlier accepted diagonal family and Cloud source branch/deletion reduction are linked. The complete five-root primitive matrix, transported polynomials and sign-separator obstruction are this packet's hand contribution. Classical finite generator calculus, convexity and polynomial separation are used; inherited mathematical controls were not rerun.
