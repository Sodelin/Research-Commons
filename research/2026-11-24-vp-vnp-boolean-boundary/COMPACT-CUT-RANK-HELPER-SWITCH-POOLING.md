# A degree-three helper is one shared switch, not two independent constraints

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and exact finite replay following the [one-auxiliary exhaustion](../2026-11-25-five-lane-parallel-pass/CHECKPOINT.md). No Lean verification or general fair-OR obstruction.

For clauses (h∨A), (¬h∨B), (¬h∨C) with independent fair selectors S,T,U and no other h-occurrence, existential elimination produces resolvents A∨B and A∨C with selectors ST and SU. A residual assignment fails to extend precisely when both h values are forbidden. This is the ordinary [Davis–Putnam resolution step](https://doi.org/10.1145/321033.321034), with the actual induced selection law carried along. The law on neither/first/second/both is (5/8,1/8,1/8,1/8), not the law of two independent quarter-probability selectors.

## Exact failure of branchwise pooling

For conditional pin tables normalized by Z11, call the remaining entries C=Z00/Z11, A=Z01/Z11 and B=Z10/Z11. Average using branch probability times the branch's Z11. Then the pooled slack for lower cross-ratio target c is
    E[C]−c E[A]E[B] = E[C−cAB]+c Cov(A,B).
The covariance need not be nonnegative. With terminal ports (x∨u),(x∨d),(y∨v),(y∨v), and internal labels (h),(¬h∨u),(¬h∨¬v),(¬u), the switch (h) off/on gives (96,96,128,128) and (50,80,60,96), respectively, in order 00,01,10,11. Every branch has cross ratio 1. The pooled table (146,176,188,224) has ratio 511/517 <1. Both branch laws are inside the declared all-fair degree-three model; the terminal y labels are distinct copies. The witness does not violate the target 1/2.

```javascript
const F=[[1,3],[1,4],[2,5],[2,5],[6],[-6,3],[-6,-5],[-3]];
const C=[0,1].map(sw=>[0,2,1,3].map(pin=>{let n=0;for(let m=0;m<256;m++){if((m>>4&1)!==sw)continue;for(let v=pin;v<64;v+=4){if(F.every((row,i)=>!(m>>i&1)||row.some(l=>!!(v>>(Math.abs(l)-1)&1)===(l>0)))){n++;break}}}return n}));
const P=C[0].map((v,i)=>v+C[1][i]);if(JSON.stringify(C)!=="[[96,96,128,128],[50,80,60,96]]"||517*P[0]*P[3]!==511*P[1]*P[2])throw Error("fixture");
```

## A sharp quantitative guarantee for one switch

Suppose two positive pin tables U and V are pooled equally, and every cell satisfies a U_xy≤V_xy≤U_xy with 0<a≤1. Write r_xy=V_xy/U_xy, d=r00 r11 and p=r01 r10. If both branch cross ratios are at least c, the pooled cross ratio is at least
    c max(1,p/d) (1+r00)(1+r11)/[(1+r01)(1+r10)]
    ≥ c (1+√a)²/[2(1+a)].
For the second inequality, first use (1+r00)(1+r11)≥(1+√d)². If d≥p, this exceeds (1+√p)²; if d≤p, multiplying by p/d gives p(1+1/√d)²≥(1+√p)². For fixed p, the other product is maximized at an endpoint pair in [a,1] (maximize r+p/r on its allowed interval). This maximum is (1+a)(1+p/a) for a²≤p≤a, and 2(1+p) for a≤p≤1. The resulting ratios decrease up to p=a and increase after it, by differentiation in √p; the minimum is the displayed factor. Equality holds for abstract tables with U cross ratio c, r00=r11=√a, r01=a, r10=1. This does not assert that an all-fair SAT gadget attains equality.

For the shared switch in the three-clause helper, use a=1/4: activating S imposes more clauses, so V≤U, and both negative selectors off, with probability 1/4, preserves every feasible S=0 residual choice. More precisely, at S=0 the two negatively signed helper clauses impose no residual condition, independently of their two selector bits. Hence V≥U/4 under the actual fair label law, pin by pin. The pooling factor is 9/10. In particular a common branch bound strictly above 5/9 proves a pooled bound strictly above 1/2 for this single step. A branch bound of merely 1/2 cannot be propagated with this estimate; multiplying 9/10 at each step is not a general invariant. To close the helper route one needs information coupling covariance with branch slack, beyond a bound on either branch alone.
