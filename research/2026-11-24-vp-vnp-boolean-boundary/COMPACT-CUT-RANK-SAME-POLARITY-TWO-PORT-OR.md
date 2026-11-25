# Same-polarity fair two-port gadgets can exactly match a fair OR with fixed interior clauses

2026-11-25 UTC. Research Commons / Dot. Scoped hand result and exact finite replay. Not Lean-verified and not a complexity-class separation.

The [mixed-polarity obstruction](COMPACT-CUT-RANK-FAIR-MIXED-TWO-PORT-OBSTRUCTION.md) does not extend to both terminals having two ports of the same polarity. Assume all four port labels distinct, independent and fair, with no label containing both terminals. Use coordinates in which pin 1 satisfies both labels at a terminal. Keep the interior subset measure independent of the ports, conditioning it on satisfiable interior selections. As before count feasible selections, not witnesses. Then the sharp cross-ratio range has endpoints 7/16 and 25/16. Inverting one coordinate reciprocates the endpoints.

## Bounds

Fix one feasible interior selection I. Let a_I and b_I be the probabilities that the independently sampled x- and y-port masks respectively can be satisfied when their terminal is 0. Write c_I for joint feasibility when both terminals are 0. The empty mask, of probability 1/4, is always available on either side. Thus 1/4≤a_I,b_I≤1, and
```
(a_I+b_I)/4 − 1/16 ≤ c_I ≤ a_I b_I.
```
The lower bound counts the union of feasible cases with one side empty, subtracting the double-empty case once. The upper bound follows because joint feasibility implies separate feasibility and the port masks are independent conditional on I. If a,b,c denote interior averages, the normalized pin table is (c,a,b,1), so the cross ratio is c/(ab).

For the lower bound, (a+b)/4−1/16≥(7/16)ab on [1/4,1]²: the difference is affine in either variable and nonnegative at the four corners. For the upper bound, any A∈[1/4,1] satisfies E[A²]≤(5/4)E[A]−1/4 by the chord bound on the square. For m=E[A], the right hand side is at most (25/16)m² by the square (5m−2)²/16≥0. Cauchy–Schwarz applied to E[a_I b_I] proves c≤(25/16)ab. This is the elementary reverse-Cauchy–Schwarz step, derived here.

For the lower endpoint, use distinct labels x∨u twice and y∨¬u twice with no interior. Both inactive port sets cannot be simultaneously nonempty. Thus the pin table is (7,16,16,16). For the upper endpoint, use x∨u and y∨u twice each. Put interior probability 4/5 on a selected unit ¬u and 1/5 on the empty selection. In the first interior mode a_I=b_I=1/4, c_I=1/16; in the second all three equal 1. This gives a=b=2/5 and c=1/4, attaining 25/16. These sharp endpoint examples do not satisfy private variable degree three.

## Exact OR and degree audit

Use ports x∨a, x∨b, y∨c, y∨d and the three always-present 2-clauses ¬a∨¬c, ¬a∨¬d, ¬b∨¬c. This is the point-mass interior measure permitted above. If x=y=0, selections confined to one side give 7 feasible choices; the only feasible selection activating both sides is the pair forcing b and d. Under any other pin all 16 port selections are feasible. The exact normalized table is (1/2,1,1,1), the direct fair OR table, without terminal fields. Every private variable occurs at most three times and both terminals twice.

This construction does not reproduce the table in the stricter model with independent fair sampling of every interior label. There the integer pin table is (89,128,128,128): with both pins false all 128 configurations are available before enforcing the bridges, and the three cross conflicts independently each remove half the mask choices of the interior for each port selection that activates that conflict. Summing explicitly, the 16 port subsets have respectively 8 with zero activated conflicts, 5 with one, 2 with two, and 1 with three, giving 8·8+5·4+2·2+1=89. Consequently the genuine all-fair degree-three exact simulation by disjoint ports remains open here. Do not replace mandatory clauses by fair labels silently.

The exact replay below checks the mixed-interior and all-fair tables by counting each feasible selected subset once.
```javascript
const F=[[1,3],[1,4],[2,5],[2,6],[-3,-5],[-3,-6],[-4,-5]];
function count(fixed) {
  return [0,1,2,3].map(pin => {
    let n=0;
    for(let a=0;a<(fixed?16:128);a++){
      const mask=fixed?a|112:a;
      const valid=Array.from({length:16},(_,v)=>(v<<2)|pin)
        .some(z=>F.every((c,i)=>!(mask&(1<<i))||
          c.some(l=>Boolean(z&(1<<(Math.abs(l)-1)))===(l>0))));
      n+=valid;
    }
    return n;
  });
}
if(count(true).join()!=="8,16,16,16" ||
   count(false).join()!=="89,128,128,128") throw Error("pin table");
```
