# An all-fair degree-three obstruction for two opposing private literal pairs

2026-11-25 UTC. Research Commons / Dot. Scoped combinatorial hand proof with exact truth-table replay. Not Lean-verified and not a separation of complexity classes.

Use the feasibility-count convention of the [same-polarity note](COMPACT-CUT-RANK-SAME-POLARITY-TWO-PORT-OR.md). Take distinct terminal labels x∨a, x∨b, y∨¬a, y∨¬b, with a,b distinct private variables. Every label incident to a or b is independently selected with probability 1/2. Assume a and b occur in at most three labels each, including the four ports. The interior labels not involving a,b may have arbitrary joint weights independent of the incident labels. They can use arbitrarily many other variables. For fixed x,y let Z_xy count feasible selected subsets with these weights (not witnesses). Then
    Z_00 Z_11 / (Z_01 Z_10) ≥ 17/32.
Equality occurs for the single interior clause ¬a∨b and no other labels. Thus this particular all-fair degree-three layout cannot simulate the fair OR cross ratio 1/2 even after positive independent scaling of the terminal rows and columns. This is not a claim about other four-port layouts.

## Condition on the rest

Fix the selected interior labels not incident to a,b and ignore selections that are internally infeasible. These have zero contribution under all pins. The private variables a,b are now initially free. Use the conditional pin table (c,u,v,1), normalized by the pin 11, for which every port subset extends. That pin also extends with all incident interior choices below, by setting the affected private literals to satisfy their incident clauses. Therefore averaging the normalized tables over the feasible rest is valid without reweighting the incident fair bits.

There can be no spare incident label, one incident label (at one or both variables), or two separate incident labels. If just one label uses both variables, with it selected at most one point of the a,b assignment square is banned. With it absent the square is full. For the both-inactive pin 00, a full square yields 9 feasible port masks out of 16: at either variable choose neither, positive, or negative, never both. Removing a single point eliminates just one of these nine masks, the one requiring both values of that point. Thus c≥(9+8)/32 and u,v≤1. This also agrees with the sharp example: ¬a∨b removes the mixed point (a,b)=(1,0), so both one-inactive pins still have full weight.

It remains to condition on two separate spare labels of forms ℓ_a∨A and ℓ_b∨B, where A,B do not mention a or b. A missing spare label can be treated as a dummy always-true clause. Write F for the full four-point square, R for its two points satisfying ℓ_a, C for its two points satisfying ℓ_b. There are five possibilities for whether A, B and A∧B can be satisfied with the fixed rest. In the four equally likely incident patterns, no label, a-label, b-label, both, the allowed sets are respectively:

| A, B, A∧B possible | Allowed assignment sets |
| --- | --- |
| 0,0,0 | F, R, C, R∩C |
| 1,0,0 | F, F, C, C |
| 0,1,0 | F, R, F, R |
| 1,1,0 | F, F, F, R∪C |
| 1,1,1 | F, F, F, F |

This follows by testing whether each selected residual clause must be satisfied by its incident literal or can be delegated to the rest. The orientation of each literal is arbitrary. Counting the 16 independent port choices for each set gives the following bounds, in units of 64, after averaging the four sets:

| Row type | 64c | Upper bound on 64(u+v) |
| --- | ---: | ---: |
| neither alone | 25 | 100 |
| exactly one alone | 30 | 112 |
| both alone but not jointly | 35 | 128 |
| jointly | 36 | 128 |

For example the 00 counts for F, R, C, R∩C, R∪C are respectively 9,6,6,4,8: for a forced value there are two consistent masks instead of three. The one-inactive combined counts in these units are at most 32,24,24,20,32 respectively: full gives 16 to each, a fixed variable gives 16 on one pin and 8 on the other (total 24), and a point gives at most 16+4 or 8+8. More directly, with one label forcing a row or column the one-inactive total is exactly 24, so the first and second bounds are 32+24+24+20=100 and 32+32+24+24=112. A union of row and column has total at most 32.

Each table row satisfies c ≥ (17/32)((u+v)/2)² by direct integer comparison. So does the single shared-label case. This stronger quadratic inequality survives arbitrary averaging over the feasible rest by Jensen, and then ((u+v)/2)²≥uv. The denominator is nonzero because the empty port masks always work. The bound follows.

## Exact replay

Enumerate each allowed subset of the four assignments against all sixteen port masks, and check the stronger integer inequality. Pin bits below are called 0,1,2,3 in binary order; exchanging the two one-inactive entries has no effect.
```js
const pins=[0,1,2,3];
function counts(S) {
 return pins.map(pin => {
  let n=0;
  for(let p=0;p<16;p++)
   if(pins.some(v=>((S>>v)&1)&&pins.every(i=>
      !((p>>i)&1)||((pin>>(i<2?0:1))&1)||
      Boolean((v>>(i%2))&1)===(i<2)))) n++;
  return n;
 });
}
const verify=a=>{if(128*a[0]*a[3]<17*(a[1]+a[2])**2)throw Error(a)};
let n=0,sharp=false;
for(let a of [5,10])for(let b of [3,12]){
 const scenarios=[
 [15,a,b,a&b],[15,15,b,b],[15,a,15,a],
 [15,15,15,a|b],[15,15,15,15],
 [15,a|b]
 ];
 for(const S of scenarios){
 const z=[0,0,0,0];
 for(const s of S)counts(s).forEach((u,i)=>z[i]+=u);
 verify(z);n++;
 if(z.join()==="17,32,32,32")sharp=true;
 }
}
if(n!==24||!sharp)throw Error("missing witness");
```
