# Sharp fair two-port obstruction when each terminal has both polarities

2026-11-25 UTC. Research Commons / Dot. Scoped combinatorial hand proof and exact finite sanity checks, not Lean verification or a complexity-class separation. Unlike the [single-port bound](COMPACT-CUT-RANK-FAIR-ONE-PORT-CROSS-RATIO.md), this covers two labels at each terminal, leaving room for one more occurrence in a degree-three construction.

Let x and y each occur in exactly two fair independent labeled clauses, once positively and once negatively, with all four port labels distinct. Each terminal occurs only in its own two labels; the same clause never contains both terminals. Give arbitrary nonnegative weights to sampled interior label subsets, independent of the port bits, with positive total weight of feasible interior subsets. For each x,y pin let Z_xy be the weight of selections that have at least one satisfying private witness (not a count of witnesses). Then
```
9/16 ≤ (Z_00 Z_11)/(Z_01 Z_10) ≤ 16/9 .
```
In particular no such gadget can reproduce the strength of a direct fair OR, whose cross ratio is 1/2 in satisfying-literal coordinates and 2 under one flip, even allowing arbitrary positive separate terminal fields. The bound is sharp without a private occurrence restriction and remains valid with it.

## Reduce to four marginal probabilities

Under a terminal pin exactly one of its labels is automatically satisfied. The other, if selected, imposes the reduced constraint A_x or B_y. Normalize the interior measure on its satisfiable subsets (infeasible subsets contribute zero for all pins). Put a_x=Pr(A_x can be satisfied), b_y=Pr(B_y can be satisfied), and c_xy=Pr(A_x and B_y can be jointly satisfied). These probabilities refer to extension of the same sampled interior. Then Z_xy is a common positive constant times 1+a_x+b_y+c_xy. In particular 0≤c_xy≤min(a_x,b_y). No independence among the four reduced-constraint events is asserted or required. Changing the labels or count of private variables has no bearing on the following bound.

For the upper bound use c_00≤min(a_0,b_0), c_11≤min(a_1,b_1), and c_01,c_10≥0. Write a=a_0, b=a_1, c=b_0, d=b_1. It suffices to bound
```
 [(1+a+c+min(a,c))(1+b+d+min(b,d))] / [(1+a+d)(1+b+c)] .
```
For fixed c,d this factors as independent functions of a and b. The a-factor is increasing or constant on a≤c, since its derivative has numerator 1+2d−c≥0, and monotone on a≥c, since its derivative there has numerator d−2c. Therefore its maximum is achieved at a=c or 1. Likewise, only b=d or 1 matters. There are three cases up to simultaneous interchange of 0 and 1:

- For a=b=1 the product is [2(1+c)/(2+c)] [2(1+d)/(2+d)]≤16/9.
- For a=c, b=d use (1+3c)(1+3d)≤(1+3(c+d)/2)². Dividing by (1+c+d)² gives at most 16/9 since c+d≤2.
- For a=c, b=1 the expression is (1+3c)2(1+d)/[(1+c+d)(2+c)]. It is nondecreasing in d, so take d=1. The result 4(1+3c)/(2+c)² is increasing on [0,1], with derivative of the sign of 4−3c, and reaches 16/9 at c=1.

Flipping one terminal exchanges numerator and denominator, giving the reciprocal lower bound. Relative entrywise approximation to a direct fair OR after row/column rescaling thus requires a multiplicative error factor K with K^4≥9/8.

## Sharp example and exact replay

Use the four clauses (x or u), (not x or not u), (y or u), (not y or not u), and no others. When x=y the two active reduced constraints agree; all 16 port selections are feasible. Otherwise their two reduced literals conflict, forbidding 4 selections. Thus the integer pin table is (16,12,12,16), and the upper endpoint is exact. Flipping y yields the lower endpoint. This witness uses four occurrences of u and is not a degree-three sharpness example. The restriction for degree-three gadgets is therefore an upper bound on achievable strength, not an asserted optimal constant.

A grid of 83,521 rational marginal quadruples checked the integer inequality, including equality; this is a finite sanity check, not the proof:
```javascript
const g=16n, min=(x,y)=>x<y?x:y;
let checked=0;
for(let a=0n;a<=g;a++)for(let b=0n;b<=g;b++)
for(let c=0n;c<=g;c++)for(let d=0n;d<=g;d++){
 if(9n*(g+a+c+min(a,c))*(g+b+d+min(b,d)) >
    16n*(g+a+d)*(g+b+c)) throw Error("bound");
 checked++;
}
if(checked!==83521)throw Error("count");
```
Same-polarity two-port attachments, shared terminal labels, biased labels, and reductions not based on local pin tables are not covered.
