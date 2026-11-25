# Exact double factor exchange on the Goldbach high-rough row

2026-11-25 UTC. Research Commons / Dot. Scoped hand identity and sharp-boundary estimate, with exact log-geometry replay. No Lean verification, positivity claim, or general signed first-moment bound.

Use the exact [factorized strict high-rough row](2026-11-24-high-rough-endpoint-sign.md), at N=2^k. Write H=sqrt(N), m=qh, n=N-m. Its q<h summand, on odd squarefree m and common box I=(H/2,H], has form

    C_N(m) mu(h) log(h/q),

where C_N(m)=F(m) A_N(N-m) sigma_N(N-m) keeps the actual original product mask, all strict endpoint and allocation tests, and the signed endpoint sum. It vanishes unless P^-(N-m)>N^(1/10), and |C_N(m)|≪log N. The fixed outer factor two can be reinserted. No independent least-prime condition on q or h is assumed here: such a condition need not survive the exchange. Every mask that is a function of m or of the endpoint allocations alone does survive.

## A four-placement identity which retains the logarithmic weight

Fix four odd pairwise coprime squarefree integers a_1,b_1,a_2,b_2 with mu(a_i) mu(b_i)=-1. Consider the union of placements on which, for each i, q contains one entire member of the pair and h contains the other entire member. This is a specified subfamily, and both exchanges preserve it at the level of the product. For example take (a_1,b_1)=(13,15), (a_2,b_2)=(79,77).

First sum over ordered q,h and divide by two; on odd squarefree m one has mu(q)=-mu(h), and log(q/h)=-log(h/q), so the two orders give the same weight. The exchange of a_i with b_i changes the sign of mu(h), holds m fixed, and adds a constant to log(h/q), independently of the other exchange. Starting at one base assignment, write the four log values as w,w+t_1,w+t_2,w+t_1+t_2. If all four ordered placements remain in the original sharp box, their signed contribution is a common scalar times

    w-(w+t_1)-(w+t_2)+(w+t_1+t_2)=0.

Equivalently the discrete mixed difference of the actual log weight is zero. This argument still applies to orbits that cross q=h: the orientation is folded only after the ordered cancellation. A single complete exchange would leave a nonzero log difference. There is no need to assume any cancellation between distinct endpoints, or to delete the actual count or mark projector on m.

## What the sharp edges cost

Put Delta=|log(a_1/b_1)|+|log(a_2/b_2)|. In any incomplete orbit, every admitted placement has at least one of q,h within log-distance Delta of an end of I. Otherwise multiplying either coordinate by any possible combined ratio, which is between exp(-Delta) and exp(Delta), would keep all placements in I. For Delta<=1, these strips have ordinary length O(Delta H). If Delta>1, use the full box, so write delta=min(1,Delta). For fixed h, the same upper sieve as in the [previous two-sided trim](2026-11-25-high-rough-two-sided-first-moment-trim.md) on the endpoint N-hq works on any interval of length O(delta H): its main term scales linearly with interval length and the CRT error does not grow. Explicitly, replace the interval length H in each residue counting main term by the actual interval length, while retaining its O(1) error per residue class; use the same cutoff R=H^(1/10) and weights. After multiplying by O(log N) for the actual grouped weights, the single-variable bound is O(delta H f(h)^2+H^(1/4)), f(h)=h/phi(h). The same estimate with q and h interchanged handles the other boundaries. Sum using sum_(h<=H) f(h)^2≪H. Thus the sharp-box signed total of the prescribed orbit family is

    O(delta N + H^(5/4)).

Dropping divisibility by the prescribed block primes in this boundary majorant is legitimate and gives an absolute implied constant independent of the ratios. All complete orbits make exactly zero contribution, not merely a small individual weight. The bound is not o(N) for a given fixed choice with nonzero Delta. It supplies no coverage claim for products without two such disjoint exchange pairs, or placements that split one of the prescribed blocks across sides. Removing or covering those complements with disjoint orbits is separate from this proof. In particular the fixed least-prime reduction does not by itself imply this extra symmetry within its individual classes.

## Exact geometry replay

This checks integer ratios, so zero log sum is verified by exact equality of two products. The fixtures are synthetic ordered sizes, not primality or target witnesses. The run covered 1,247 base pairs, 425 complete box orbits, and 333 complete orbits that cross q=h. Replace text by console.log outside the replay environment.

```javascript
const A=[13n,79n],B=[15n,77n];let checked=0,full=0,switched=0;
for(let Q=100n;Q<=185n;Q+=2n)for(let R=100n;R<=185n;R+=3n){
  let n=1n,d=1n,k=0,first=new Set();
  for(let t=0;t<4;t++){
    let q=Q,h=R;
    for(let i=0;i<2;i++){q*=t>>i&1?B[i]:A[i];h*=t>>i&1?A[i]:B[i];}
    if(2n*q<=270000n||q>270000n||2n*h<=270000n||h>270000n)continue;
    if((t===0||t===3)){n*=h;d*=q;}else{n*=q;d*=h;}
    k++;first.add(q<h);
  }
  if(k===4){if(n!==d)throw Error("log cancellation");full++;if(first.size===2)switched++;}
  checked++;
}
if(!full||!switched)throw Error("missing witness");
text({checked,full,switched});
```
