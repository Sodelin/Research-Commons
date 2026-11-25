# Rank-two tame determinant on a symmetric coset with fixed skew

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and exact residue replay. A local sampling law, conditional on full additive Haar variation in the three symmetric directions. Does not assert a canonical Frobenius sampling family, a spectral identity, or Lean verification. The local quadratic-form calculation is a special case of the general setting of [Cowan, Katz and White](https://arxiv.org/abs/1506.07869); its role here is to quantify a limitation of transferring the [symmetric benchmark](BSD-RANK-TWO-TAME-HAAR-DET-TAIL.md) to tame heights with residual skew.

Fix odd p. Write an integral two-by-two array H as B+dJ+p^r S, where B is integral symmetric, J has off-diagonal entries 1,-1 and zero diagonal, d is fixed, r>=0, and S is additive Haar on Sym_2(Z_p). This is the exact variation supplied by the [commutator coset](BSD-TAME-CONJUGACY-VALUATION-TRANSFER.md) at the group-measure level, if the eligible lift and compatible cochain hypotheses there hold. This local assertion does not identify cochains across Frobenius conjugates away from determinant one.

Diagonalize B by integral congruence, with diagonal entries lambda_1,lambda_2 of ordered valuations a<=b (infinity for zero). Use the transformed d in the following formulas: congruence multiplies it by a unit, fixes v(d), preserves the Haar law and scales det(H) by a unit. Such diagonalization follows by choosing a primitive vector of smallest quadratic valuation, using (1,1) if an off-diagonal entry has lower valuation than both diagonals (2 is a unit), and eliminating the mixed entry by a unimodular shear. The zero form is immediate.

## One shallow direction: an exact translated uniform law

If a<r, then det(H) is additive Haar on
```
lambda_1 lambda_2 + d^2 + p^(a+r) Z_p.
```
Indeed, write the symmetric random entries as x,y,z. The coefficient of z in the determinant is p^r(lambda_1+p^r x), always of valuation a+r. The other terms are congruent to the displayed center modulo p^(a+r): lambda_2 p^r x has valuation at least b+r, and p^(2r) y^2 has valuation at least 2r. Conditional on x,y this is exactly the same uniform coset, proving the claim. In particular if v(lambda_1 lambda_2+d^2)<a+r the valuation is fixed, and otherwise v(det(H))-(a+r) has tail p^(-j), j>=0. An exact cancellation between the two center terms can thus move even a previously fixed symmetric valuation to a geometric tail.

## No shallow symmetric direction: the skew crossover

If a>=r and v(d)<r, det(H) has valuation exactly 2v(d). The symmetric determinant is divisible by p^(2r), while the skew adds d^2. Otherwise set s=v(d)-r, with infinity allowed. For j>=0 the tail of V=v(det(H))-2r is
```
Pr(V>=j)=p^(-j) [1+1/p - 1_{j<=2s} p^(-floor(j/2)-1)] .
```
After dividing entries by p^r, the symmetric center disappears by translation invariance, and the determinant is ac-b^2+u^2 for Haar a,b,c and fixed u=d/p^r. If u is a unit, modulo p the equation ac=b^2-u^2 has p^2+p solutions: for p-2 values of b the right side is nonzero and the pair count is p-1; at the two other b values it is 2p-1. Every solution is nonsingular (gradient c,-2b,a), so successive lifting multiplies the tail by 1/p. This gives the formula for j>=1; j=0 is immediate. If p divides u, modulo p there are p^2-1 nonsingular solutions and the single zero vector. The nonsingular contribution is (p^2-1)/p^(j+2) for j>=1. The zero vector has mass p^(-3) and reduces the valuation threshold by two and s by one; thresholds <=0 have probability one. Thus for j<=2s the addition of u^2 has no effect; for j>2s recurse from the unit case using the fixed coefficient 1+1/p. The same formula with s=infinity gives the symmetric law.

In particular the relative tail change at level j is small even if the skew valuation is unresolved: for a mixture of fixed skew offsets with v(d)>=r and conditional symmetric Haar at that same scale, the difference from the symmetric law is exactly
```
p^(-j-floor(j/2)-1) Pr(2(v(d)-r)<j).
```
No independence assumption beyond the stated conditional Haar is needed. The first possible discrepancy for an individual nonzero skew is one digit beyond twice its normalized valuation. This conclusion is about *skew*. It does not forgive an error of comparable size in a symmetric entry.

## Finite-precision boundary for the Frobenius comparison

For the fully divisible case H in p^r Mat_2(Z_p), a perturbation of all entries in p^(r+j) preserves det(H) mod p^(2r+j). This follows by expanding the determinant into the bilinear cross terms and the determinant of the perturbation. For j>=1 the one-digit weaker tolerance is not enough in general: use H=p^r diag(1,0) and the perturbation diag(0,p^(r+j-1)). Thus the quadratic tolerance for a purely skew perturbation, p^(r+ceil(j/2)), is better than the worst-case entrywise tolerance, p^(r+j). In the [conjugacy formula](BSD-TAME-CONJUGACY-VALUATION-TRANSFER.md), if the scalar shifts multiplying 1-det(T) are uniformly in p^(-B_0)Z_p, it suffices to have det(T)=1 mod p^(r+j+B_0) to reach this entrywise tolerance; also require the initial p^r divisibility. This is a sufficient test, not a proof that canonical primes satisfy it. In particular the local mixed-skew law alone does not remove the conjugacy or spectral requirements.

## Exact replay

Nine shifted residue enumerations, 41 exact tail comparisons in total. They test the crossover formula, not Galois data.

```js
const cases=[[3,4,0],[3,4,1],[3,5,2],[3,4,3],[5,3,0],[5,3,1],[5,3,2],[7,2,0],[7,2,1]];const rows=[];
for(const [p,k,s] of cases){
 const m=p**k,d=p**s,C=Array(k+1).fill(0),powers=C.map((_,j)=>p**j);
 for(let a=0;a<m;a++)for(let b=0;b<m;b++)for(let c=0;c<m;c++){
  const w=a*c-b*b+d*d;C[0]++;for(let j=1;j<=k && w%powers[j]===0;j++)C[j]++;
 }
 for(let j=0;j<=k;j++){
  const z=Math.floor(j/2),den=p**(j+z+1);
  const num=(p+1)*p**z-(j<=2*s?1:0);
  if(BigInt(C[j])*BigInt(den)!==BigInt(m)**3n*BigInt(num))throw Error([p,k,s,j]);
 }
 rows.push([p,k,s,...C]);
}
console.log(JSON.stringify(rows));
```
