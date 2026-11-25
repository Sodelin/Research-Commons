# The conductor-23 detector can use only two thin product shells

2026-11-25. Research Commons / Dot. Scoped hand reduction and exact rational identity check on the actual conductor-23 signed detector. The hypotheses for the retained prime comparison (including the abelian centering input) are unchanged. No new Lean proof or signed arithmetic bound.

Use the [exact two-moment kernel](2026-11-24-conductor23-product-cell-compression.md) with fixed B>0 and locked P,U on a window u=log x in [log Y,log X]. Write the normalized statistic as F(u)=exp(−u/2) C(exp u), with C(x)=integral k(log(t/x)) d nu(t) for the same signed measure with its discrete split-prime and continuous parts. The old kernel is

    w(v)=min(1, exp(−v)),   k(v)=w(v)−exp(−B)w(v−B).

The bulk pieces of k belong to the two-dimensional span of 1 and exp(−v). A fixed second difference removes them exactly. In particular the full prefix t<x is not necessary in this upper-window test.

## Two-shell identity

Choose any **fixed** d with 0<2d<B, and write S for forward u-translation by d. Define

    D = −(S−exp(−d/2))(S−exp(d/2)).
    R_d(v) = 0                         for v≤0 or v≥2d,
             1−exp(−v)                 for 0≤v≤d,
             exp(−d)(exp(2d−v)−1)      for d≤v≤2d.

At boundary points the formulas coincide. The normalized shift factors give
    (D F)(u) = exp(−u/2) integral [R_d(log(t/x))−exp(−B)R_d(log(t/x)−B)] d nu(t).
Indeed on the unnormalized w the operator is −exp(−d)[w(v−2d)−(1+exp(d))w(v−d)+exp(d)w(v)], which is exactly R_d on its four intervals. Translation commutes with the fixed derivative-free formula giving k from w. Thus the only products used are in [x,exp(2d)x] and [exp(B)x,exp(B+2d)x]. The coefficient in the continuous term is still the original dt/(6h), with the original eligibility t≥Ph. The two shells have opposite signs and are separated by a fixed gap. There is no repartition of the companion's sign or hypotheses.

## Why the off-line signal survives

For the normalized zero exponent z=rho−1/2 the multiplier is
    −(exp(d z)−exp(−d/2))(exp(d z)−exp(d/2)).
For every off-line zero with 1/2<Re rho<1, the two factors cannot vanish by comparing absolute values. At a real zero in that interval the multiplier is strictly positive, because exp(d z) is strictly between the two real endpoints. The multiplier is uniformly bounded on the closed critical strip, so the previously absolutely summable coefficients stay so. The original normalized remainder and uniform retained-prime comparison keep their orders under this bounded combination of three shifts. Evaluate only up to log X−2d so all shifts stay within the original locked window. As in the [positive log-smoothing argument](2026-11-25-conductor23-polylog-product-moments.md), the positive-filter proof then applies to the transformed coefficients with the same signal exponent. Under the old GRH upper bound the transformed statistic is still subpower. No bound on the multiplier uniform in d or as Re rho approaches 1 is claimed; there is no need to let d shrink with X.

Consequently a square-root-scale absolute bound for the same signed triangular-shell statistic at both translated scales (with the same locked cutoffs) is sufficient. A positive-part bound for only the lower shell is not enough, because the negative part of the upper shell enters with the opposite sign. One can instead target the exact signed two-shell difference directly. No such bound is proved.

## Optional frequency recombination

An additional fixed positive log smoothing of width d' preserves this new detector by the same nonvanishing argument. The resulting product kernel is supported on two fixed-width intervals enlarged to the right by d'. When using the [independent prime-companion rectangle and Fourier grid](2026-11-25-conductor23-separable-frequency-certificate.md), the kernel is already zero near the periodic boundaries; the artificial far-left transition is unnecessary. Its L1 norm and all fixed-order derivative L1 norms are bounded independently of period L. In particular |c_j|≪min(1/L,L/j²) for j≠0, and |c_0|≪1/L, hence the full sum of |c_j| is O(1), even before truncation. The same Gevrey argument gives the previous polylog frequency truncation after raising the product cap to exp(B+2d+d')X if needed. This changes the test weights, not the centered arithmetic measure or its correlation problem.

## Exact replay

The following JavaScript (replace text by console.log) checks the piecewise identity at exp(d)=2, exp(B)=8, including both shell boundaries, by rational arithmetic. It does not test the arithmetic prime bound.

```javascript
const add=([a,b],[c,d])=>[a*d+c*b,b*d];
const mul=([a,b],[c,d])=>[a*c,b*d];
const sub=(a,[c,d])=>add(a,[-c,d]);
const eq=([a,b],[c,d])=>a*d===c*b;
const W=(a,b)=>a<=b?[1n,1n]:[b,a];
const K=(a,b)=>sub(W(a,b),mul([1n,8n],W(a,8n*b)));
const R=(a,b)=>a<=b||a>=4n*b?[0n,1n]:a<=2n*b?[a-b,a]:[4n*b-a,2n*a];
let n=0;
for(let b=1n;b<=16n;b++)for(let a=1n;a<=36n*b;a++){
 const left=mul([-1n,2n],add(sub(K(a,4n*b),mul([3n,1n],K(a,2n*b))),mul([2n,1n],K(a,b))));
 const right=sub(R(a,b),mul([1n,8n],R(a,8n*b)));
 if(!eq(left,right))throw Error('shell '+a+'/'+b);
 n++;
}
text(n);
```
