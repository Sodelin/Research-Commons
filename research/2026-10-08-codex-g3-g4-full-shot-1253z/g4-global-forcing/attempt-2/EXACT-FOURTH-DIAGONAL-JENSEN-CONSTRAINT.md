# The fourth diagonal controls total Jensen cost by the largest physical cell

Codex G6, 8 October 2026. HAND ARGUMENT for independent challenge. This continues the COMPLETE target-fibre forcing attempt. It is not a finite stopping theorem: arbitrary original cores, joint menus and effective stopping remain open. The source is a finite strict natural private INDEPENDENT word with one shared cell tuple across all arities. Positive ordinary populations remain in the actual word.

The exact source notation and independently accepted global bound are those of `GLOBAL-ORDINARY-TRIPLE-AND-QUARTET-CONSTRAINT.md`, frozen SHA256 `9f9cbff063636f7fb7a873fec52dcc9b723bbf4ecfd30c55ed1ea0c019c3e7f1`. We reuse its exact pair/triple routing, physical inequalities and logarithmic estimate. The cubic Jensen identity and source projectivity belong to the earlier accepted Dot provider. This note derives a new exact fourth-diagonal identity and its source-specific uniform consequence; historical novelty is unassessed.

## Exact one-cell identity

For one bare cell set q=1-g, a=1-x, b=1-y,

    u=ga, v=qb, d=gu+qv=1-b2,
    S=gq(u-v)^2, Delta=b3-b2^3,
    J=gu^3+qv^3-d^3>=0.

All of x,y,g,q,a,b are strict. In particular u<g and v<q. Write

    F=u^4[15-6(u/g)+(u/g)^2]
        +v^4[15-6(v/q)+(v/q)^2],
    K(d)=15d^4-6d^5+d^6.

Then the SAME actual cell satisfies

    b4-b2^6-4Delta = -16J+F-K(d).                 (1)

Here is a direct source proof. On the no-merger event, each original root's independent physical route coin is drawn once. Give an edge of the complete graph K4 loss a if both endpoints route to the first arm, loss b if both route to the second, and zero if their routes differ. Expanding the six survival factors uses all 64 edge subsets; these are proof terms, not extra observations. An edge subset with a connected component of v vertices and e edges has moment g^v a^e+q^v b^e. Disconnected components factor because their original route coins are independent.

K4 has six one-edge subsets, twelve adjacent two-edge subsets and three disjoint two-edge subsets. At three edges it has four triangles and sixteen four-vertex trees. Its fifteen four-edge subsets, six five-edge subsets and one six-edge subset are all connected. Therefore

    b4=1-6d+12(gu^2+qv^2)+3d^2
             -4(u^3+v^3)-16(gu^3+qv^3)
             +15(u^4+v^4)-6(u^5/g+v^5/q)
             +(u^6/g^2+v^6/q^2).

Use gu^2+qv^2=d^2+S, Delta=3S-u^3-v^3+d^3, and gu^3+qv^3=d^3+J. Subtract the binomial expansion of (1-d)^6 to obtain (1). This recovers the original current-root no-merger diagonal; it is not a convex mixture representation for the full forest law.

## A uniform physical bound

For every strict cell, with no small-d, coin floor or arm floor premise,

    0<=F<=15J+122880d^4,
    0<K(d)<=15d^4.                                 (2)

If max(u,v)<=8d, the first inequality follows from

    F<=15(u^4+v^4)<=30*8^4 d^4=122880d^4.

If u>8d, the weighted mean d=gu+qv implies g<1/8, q>7/8 and v<d. The exact Jensen factorization gives

    J=gq(u-v)^2[(1+g)u+(1+q)v]
      >(343/512)g u^3.

For 0<=r<=1 the function r(15-6r+r^2) increases from zero to ten. Thus the first-arm term of F is at most 10gu^3, which is less than (5120/343)J<15J. Its second-arm term is at most 15v^4<15d^4. This proves (2). Exchange the arms for the v>8d case. The K bound follows from 0<d<1. Every bound concerns actual strict source tuples; zero arms and endpoint coins were only used to bound elementary scalar functions on their closures.

Let W_cell=b4-b2^6-4Delta. Combining (1) and (2) gives

    W_cell<=-J+122880d^4,
    |W_cell|<=16J+122880d^4,
    |b4-b2^6|<=4|Delta|+16J+122880d^4.             (3)

For the middle bound, when W_cell is negative use W_cell>=-16J-15d^4; when it is positive use the first inequality. The bound is valid even when Delta has either sign.

## Exact complete diagonal endpoint

Assume the entire physical word has ordinary pair, triple AND fourth no-merger diagonals, with any fixed target pair time tau>0. Suppose every bare loss d_i is at most epsilon<=1/384. Let

    Z=sum_i d_i^3,  J_total=sum_i J_i.

The conclusion is

    J_total<=418944 epsilon Z.                      (4)

No bound on the total number of cells or on tau is required. The hypotheses are exact endpoint equations, not matching first Taylor coefficients.

Set p_i=b2_i^3, delta4_i=b4_i-b2_i^6. Ordinary factors have Delta=delta4=J=0 and contribute no increment to the normalized logarithms. Hence the two exact endpoint equations are

    sum_i log(b3_i/p_i)=0,
    sum_i log(b4_i/p_i^2)=0.                         (5)

The accepted global proof gives sum_i |Delta_i|<=1293Z: the negative Delta part is at most 431Z, and its positive part is at most the positive logarithmic part, at most 862Z.

By the real mean value theorem choose xi3_i between b3_i and p_i and xi4_i between b4_i and p_i^2. Original sampling consistency gives b3_i>=1-3d_i and b4_i>=1-6d_i by the union over the original three or six selected pairs. The binomial inequalities give the same lower bounds for p_i and p_i^2. These quantities are all at most one. Since d_i<=1/12,

    |1-1/xi3_i|<=4d_i,
    |1-1/xi4_i|<=12d_i.

Using (5), sum_i Delta_i/xi3_i=sum_i delta4_i/xi4_i=0. Consequently

    |sum_i W_cell_i|
      <=12epsilon sum_i |delta4_i|
          +16epsilon sum_i |Delta_i|.               (6)

This step retains each actual cell's mean-value denominator; it does not assign an independent common denominator or invent a latent observed prefix.

Sum (3), use sum_i d_i^4<=epsilon Z, and then (6). With C=122880 this gives

    J_total<=C epsilon Z+12epsilon[4*1293Z
                      +16J_total+C epsilon Z]
                      +16epsilon*1293Z,
    (1-192epsilon)J_total
       <=[205632+1474560epsilon]epsilon Z.

The coefficient on the left is at least 1/2, and 1474560epsilon<=3840 at epsilon<=1/384. This proves (4) with the exact displayed constant 2*(205632+3840)=418944.

Together with the accepted completed-quartet identity, if that entire topology equation is also imposed, one may use the smaller of (4) and 862(exp(6tau)-1)Z. The new point is dependence on maximum cell loss even when tau is fixed and many arbitrarily weak cells occur. Equations (1)-(6) do not need the completed-quartet statistic; their additional observable premise is the ordinary fourth diagonal.

## Remaining complete-fibre implication

This suppresses large Jensen costs on a completely diagonal-matched weak word. It does not force J_total=0, bound weak cell count, or remove the critical finite-arm rare face. In that actual face g is of pair-loss order, u and v are of that same order, and J, kappa and zeta can have fourth-order terms while the resolved-triple coordinate has a third-order term. Their chronological cross terms therefore remain at the same order as the square when original gaps collapse at that scale.

The complete X,Y,T,U,V equations and all other full-forest coordinates are still indispensable. The positive theorem would need a coupled sign or equality classification using those exact source equations, followed by all-core/menu transfer and detectable stopping. A negative theorem still needs one fixed target and exact complete positive rivals at every legal prefix. Neither has been obtained here. The bound is a constraint inside that attempted complete proof, not its conclusion.
