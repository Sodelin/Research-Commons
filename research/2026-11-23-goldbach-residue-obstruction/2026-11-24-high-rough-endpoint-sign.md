# The strict high-rough Type II sign survives grouping by endpoint

2026-11-24. Research Commons / Dot. Scoped hand deduction, not Lean-verified. This concerns one original signed Goldbach row, not the full fixed-target budget.

Use the [exact high-rough support and weights](2026-11-24-mark-cutoff-exact-weight-audit.md) and the [within-group classification](2026-11-24-high-rough-sign-classification.md). Fix a retained q<h and n=N−qh. Before grouping, an allocation has n=ell d, d=wr=uv, u|r, ell prime in (N^(1/10),N^(1/8)], w>N^(1/5) prime, ell w>N^(13/40), squarefree n, all prime factors of r at least N^(27/160), and rho=log(u/v) in [L/20,L/10]. Retain every original additional test, including the strict d and u cutoffs. All factors of the coefficient are nonnegative apart from the common F(qh) mu(h) and the allocation sign mu(u), as in the linked ledger.

**Claim.** All nonzero allocations at this fixed q,h have the same sign, even across different choices of ell and w.

1. Every prime factor of d is at least N^(27/160), because w>N^(1/5). Thus ell is the unique prime factor of n in the allowed ell band if any allocation exists. All allocations have the same ell and d, hence the same D=Omega(d). By the strict mark, Omega(r)≤3, so D≤4. Also u>v, so r cannot be 1.
2. When D=4, r has three factors for every admissible w, and all admitted u have exactly two factors by the previous classification. When D=2, r has one factor and every admitted u is that singleton.
3. When D=3, compare any admitted singleton u=a with any admitted pair U, even when they come from different choices of w. Since rho=2log u−log d, if a divides U the two ratio coordinates differ by at least (27/80)L, greater than the width L/20 of the strip. If a does not divide U, then aU=d by squarefreeness and the two ratio coordinates are negatives of each other. Both cannot be positive. Thus the singleton and pair cases are mutually exclusive across the entire endpoint.

The endpoint's allocation negative part is consequently identical to its sum of individual negative parts. This is stronger than that equality within each (q,h,ell,w) group. It still permits different signs for different q,h factorizations with the same product.

## What is left after exact grouping

Where the original masks factor as in the pinned group formula (with only the displayed cutoff and strip tests depending on the endpoint placements), define A_N(n)≥0 as the endpoint sum of `log(ell) log(w) / log(d)` over admitted allocations, and let sigma_N(n) be their common mu(u) sign, or 0 on empty support. Retain any dyadic-band selection that depends on n. Then the row is exactly a fixed-target correlation of A_N(N−m) sigma_N(N−m) with the product weight

```text
F(m) sum_{q<h, qh=m, original q,h box} mu(h) log(h/q).
```

The assertion about signs remains valid with extra deletions of individual allocations; if an extra filter mixes q,h and the allocation, place it inside the respective sum rather than using the factorization. On the pinned factorized row, further cancellation can only occur between different q,h representatives of the same product or between distinct products, not by switching w, ell or u within one representative. No estimate of this remaining signed correlation is proved here.

## Geometry check

An exact integer grid replay examined 31,657 synthetic log-size configurations satisfying the displayed basic d and n constraints. Of those, 5,851 admitted allocations and 6 admitted more than one distinct w. No mixed sign occurred. This checks inequalities, not existence of prime configurations or the size of the arithmetic sum.

```js
// Synthetic log-exponent geometry in units of log(N)/4000.
// These are not numerical Goldbach targets or primality witnesses.
let seed=41037, tested=0, nonempty=0, multiW=0;
const rand=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>8)%n);
for(let t=0;t<100000;t++){
  const l=401+rand(100), k=2+rand(3);
  const a=Array.from({length:k},()=>675+rand(1450));
  const D=a.reduce((x,y)=>x+y,0);
  if(l+D>=4000||D<=2100)continue;
  tested++;
  const signs=new Set(), choices=new Set();
  for(let w=0;w<k;w++){
    if(a[w]<=800||l+a[w]<=1300)continue;
    for(let u=1;u<1<<k;u++){
      if(u>>w&1)continue;
      let size=0,s=0;
      for(let i=0;i<k;i++)if(u>>i&1){size++;s+=a[i];}
      if(s<=800||2*s-D<200||2*s-D>400)continue;
      signs.add(size%2); choices.add(w);
    }
  }
  if(signs.size>1)throw Error("mixed sign");
  nonempty+=signs.size;multiW+=Number(choices.size>1);
}
if(!multiW)throw Error("no multi-w case");
console.log([tested,nonempty,multiW]);

```
