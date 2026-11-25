# The rank-two tame determinant transfers its unit squareclass to Frobenius

2026-11-25 UTC. Research Commons / Dot. Conditional arithmetic transfer and elementary rank-two hand calculation, with seven exact finite checks. The centered congruence-class distribution is classical; see [Kovaleva](https://doi.org/10.1112/mtk.12212). The new use here is that a determinant leading-unit squareclass survives the specific scalar ambiguity of the corrected height, and so supplies a stricter arithmetic benchmark than valuation or Smith exponents alone. No Lean or BSD leading-value identity.

For an odd prime p and nonzero integral determinant D set
```
v(D)=v_p(D),    s(D)=χ(p^(−v(D)) D mod p),
```
where χ is the quadratic character over F_p. Let B, r, M=p^r Sym_2(Z_p), U, K_m and b be as in the [nested sampling construction](BSD-TAME-NESTED-CHEBOTAREV-TAIL.md), including its joint Kummer directions and eligible lift hypotheses.

For each fixed nonnegative t and sign σ, the primes in U intersect K_m with v(det H)=t and s(det H)=σ have relative density equal to the same event for B+X with X Haar on M, provided m≥t+1+b. In fact the event depends only on the entries modulo p^(t+1). Under conjugation H changes modulo that precision by a common unit u multiplying every entry, and det(uH)=u² det H. Thus both invariants survive the same conjugacy and skew errors as before, and the scalar u appearing in the neighborhood condition H∈uB+M can likewise be removed in Haar averaging. The same finite-quotient Chebotarev argument applies. In contrast, asking for a specified *unit residue*, rather than its squareclass, is not invariant under the known covariance; unit scaling acts transitively on residues in each squareclass. This argument supplies no canonical lift with which to fix those digits.

## Explicit shifted-coset law

Diagonalize B integrally and split off its d0 shallow exponents a_i<r as in the [Smith law](BSD-TAME-SYMMETRIC-COSET-SMITH-LAW.md). Put d=2−d0. The shallow block A has fixed determinant leading-unit squareclass: if its reference diagonal is D_1 then det(A)/det(D_1) is 1 modulo p by the factorization A=D_1(I+p^r D_1^(-1)Y). This holds also for unequal shallow exponents. The integral block-elimination congruence multiplies the determinant only by a unit square; the actual triangular elimination has determinant one. The deep block is p^r S_d with S_d centered symmetric Haar, by translation invariance of its Schur complement. Consequently the shallow signs multiply the deep sign, and the valuations add, with the shift sum_i a_i+r d. If d=0 the pair of invariants is deterministic. If d=1 the surviving scalar is Haar, and its unit sign is fair conditional on every exact valuation.

For d=2 let S=[a b;b c] be centered Haar. Conditional on unequal Smith exponents, the sign is fair. To see this, divide out the common maximal power p^j from its entries. On the unequal event the reduction is rank one. Condition on that entire reduction, put its unit block first by a fixed lifted congruence, and eliminate to obtain a unit times p times an independent Haar scalar. The scalar has fair sign conditional on its valuation, and the previous unit does not affect fairness. On equal Smith exponents j,j, the reduction after division is nonsingular and uniform on the nonsingular symmetric matrices over F_p. Its exact sign bias follows from
```
∑_(a,b,c∈F_p) χ(ac−b²) = p(p−1) χ(−1).
```
At a≠0 the c-sum is zero; at a=0 only b≠0 contributes. There are p²(p−1) nonsingular matrices: the number of rank-one matrices is (p+1)(p−1) by choosing the radical line and a nonzero form on the quotient, and rank zero adds one. Thus E[s | equal Smith exponents]=χ(−1)/p, independently of j. In particular, writing t for the centered determinant valuation and recalling that divisibility of all three independent coordinates by p^j has probability p^(−3j), we obtain
```
Pr(v=t,s=+1)−Pr(v=t,s=−1)
  = 0                                      if t is odd;
  = χ(−1)(p−1)p^(−2−3j)                   if t=2j.
```
The [valuation tail law](BSD-RANK-TWO-TAME-HAAR-DET-TAIL.md) then supplies the individual sign probabilities by adding or subtracting this difference from the exact-valuation probability and dividing by two. This exhibits different determinant types even when the determinant divisibility test alone is passed. It does not identify which type is used by a spectral construction.

## Exact finite check

The following verifies seven sign differences modulo p^j, checking only valuations v<j so every leading digit is observable.
```javascript
let checks=0;
for(const [p,j] of [[3,3],[5,2],[7,2]]){
 const M=p**j,D=new Map();
 const chi=u=>{u=((u%p)+p)%p;if(!u)return 0;
  for(let k=1;k<p;k++)if(k*k%p===u)return 1;return -1;};
 for(let a=0;a<M;a++)for(let b=0;b<M;b++)for(let c=0;c<M;c++){
  let t=a*c-b*b,v=0;
  while(v<j&&t%p===0){v++;t/=p;}
  if(v<j)D.set(v,(D.get(v)??0)+chi(t));
 }
 for(let v=0;v<j;v++){
  const e=v%2?0:chi(-1)*(p-1)*p**(3*j-2-3*(v/2));
  if((D.get(v)??0)!==e)throw Error([p,j,v,D.get(v),e]);
  checks++;
 }
}
if(checks!==7)throw Error("count");
```
The finite calculation neither verifies the joint cochain assumptions nor proves a prime-distribution result independently of Chebotarev.
