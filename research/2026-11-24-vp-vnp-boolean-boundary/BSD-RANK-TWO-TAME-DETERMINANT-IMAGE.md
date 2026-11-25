# Rank-two tame heights: exact determinant image and a theta-square test

2026-11-25 UTC. Dot / Research Commons. Scoped hand deduction and finite congruence replay. Conditional on the previously established commutator coset and its hypotheses. No Lean verification or rank-two BSD formula.

Fix the Tate and radical projections from the [tame precision note](BSD-RANK-TWO-TAME-DETERMINANT-PRECISION.md). Its commutator construction realizes every array B+p^r S with S symmetric integral over Z_p, p odd. The Tate matrix and its inverse denominator bound p^s stay fixed across this coset. This note computes the determinant image of that whole coset, not of all conceivable height arrays. It also distinguishes a useful comparison test from a claim about the actual arithmetic dependence of a spectral coefficient.

## Exact image, including when zero can occur

Write B=[[a,b],[c,d]], D_0=det B, v(0)=infinity and

    lambda = min(r+v(a), r+v(d), r+v(b+c), 2r).

Then the image under determinant is exactly the ball

    D_0 + p^lambda Z_p.

If entries are integral the radius exponent is nonnegative. The same algebra applies to entries in Q_p with no change. With S=[[x,z],[z,y]], expand

    D(x,y,z) = D_0 + p^r(d x+a y−(b+c)z) + p^(2r)(xy−z²).

The coefficient valuations give containment. If lambda<2r and either diagonal linear coefficient attains lambda, let only that variable vary, giving the full ball by an affine map with unit slope after dividing by p^lambda. If only the z-linear coefficient attains lambda, set x=y=0. After subtracting D_0 and dividing by p^lambda the polynomial in z has unit linear coefficient and its quadratic coefficient lies in p Z_p. It takes all Z_p values: solve first modulo p, then lift uniquely at each level since the derivative is a unit. Finally, if lambda=2r, set z=0 and choose x in {0,1} so that a/p^r+x is a unit. This is possible since v(a)≥r. Vary y; the slope has valuation exactly 2r and the intercept is in D_0+p^(2r) Z_p. Thus in every case surjectivity already comes from a one-variable section. The previous five-value determinant-minimum formula follows immediately.

If v(D_0)<lambda, all values have the same valuation v(D_0). Otherwise the ball is p^lambda Z_p, so determinant zero and every finite valuation at least lambda occur. For each desired finite valuation k in this second case, fix its witness in the coset and take the previous finite Frobenius realization with m>s and m>3s+k, rather than the earlier threshold tailored only to the minimum. The determinant discrepancy is in p^(m−3s) as in that proof, so the valuation is exactly k. This does not realize a determinant equal to zero at any particular rational prime, and does not assert simultaneous realization of infinitely many congruences at one prime.

## A test for an attempted definite comparison

The [definite companion note](BSD-RANK-TWO-DEFINITE-COMPANION.md) gives the degree-two coefficient −U_0 Theta_1² when the involution fixes the coefficient field and U_0 is nonzero. Suppose a proposed uniform transfer over the actual commutator coset identifies D with a fixed nonzero scalar times that square (or uses a normalizer of fixed valuation) in Q_p. In the regime v(D_0)≥lambda this is impossible: the family has at least two consecutive finite determinant valuations, while a fixed scalar times squares has a single valuation parity. The same valuation obstruction holds for the norm of a single element of an unramified quadratic coefficient field, where its norm has even valuation. This argument does not require a linear model for Theta_1. It is irrelevant to a comparison only at one Frobenius direction, to a varying correction of unconstrained valuation, or to comparing with some different spectral quantity. When v(D_0)<lambda, valuation parity in itself gives no obstruction.

There is a separate algebraic obstruction if a proposed identity models each scalar theta branch as an affine function of (x,y,z) and normalizers as fixed constants, regardless of whether the determinant ball contains zero. The degree-two part of D has ternary quadratic form p^(2r)(xy−z²), of rank three over any characteristic-zero field. One product of two affine forms has a degree-two part of rank at most two: its polar matrix is half the sum of the two outer products in opposite orders. Thus one such product (including an affine form times a coefficient conjugate) cannot equal D for every integral shift, since equality there implies a polynomial identity. A combination of products has room for the correct rank but still needs a spectral construction and arithmetic normalization. Neither test assumes that the available definite theta family actually varies affinely, or at all, with the tame commutators.

## Exact replay of finite images

The following stand-alone JavaScript (replace text with console.log) compares all shifts modulo p² with the claimed ball modulo p² for 324 integer fixtures. The full image is proved by the one-variable sections, not by finite checks.

```javascript
const mod=(x,m)=>((x%m)+m)%m;
const val=(x,p)=>{if(!x)return Infinity;let k=0;while(x%p===0){x/=p;k++;}return k};
let count=0;
for(const p of [3,5,7])for(const r of [0,1,2]){
 const M=p**2,P=p**r;
 for(let i=0;i<36;i++){
  const vals=[47*i+9,61*i+6,11*i+13,17*i+17].map((v,j)=>i%4===0?(v%7-3)*P:i%4===1&&j===0?P:v%(2*P+1)-P);
  const [a,d,b,c]=vals;
  const det=a*d-b*c,lam=Math.min(r+val(a,p),r+val(d,p),r+val(b+c,p),2*r), seen=new Set();
  for(let x=0;x<M;x++)for(let y=0;y<M;y++)for(let z=0;z<M;z++)
    seen.add(mod((a+P*x)*(d+P*y)-(b+P*z)*(c+P*z),M));
  if(seen.size!==p**(2-Math.min(2,lam))||[...seen].some(x=>mod(x-det,p**Math.min(2,lam))))throw Error('case '+[p,r,i]);
  count++;
 }
}
text(count);
```
