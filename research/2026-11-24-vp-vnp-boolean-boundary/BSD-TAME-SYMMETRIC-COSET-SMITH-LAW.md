# Full elementary-divisor benchmark on symmetric tame-height cosets

2026-11-25 UTC. Research Commons / Dot. Scoped hand reduction and 15 finite determinant checks. The centered symmetric-matrix law is classical; see [Kovaleva's distribution of equivalence classes](https://arxiv.org/abs/2008.10732). The use here is to replace a shifted tame-height coset by a centered, smaller matrix for *all* elementary divisors at once. Conditional on an actual symmetric Haar coset when used for cochains. No Lean verification, canonical spectral sampling, or BSD leading-value identity.

Let p be odd, B integral symmetric of size n, and S additive Haar on Sym_n(Z_p). Fix r>=0 and H=B+p^r S. Diagonalize B by a unimodular congruence and order its diagonal valuations. Let a_1<=...<=a_k<r be all valuations strictly below r (zero entries have valuation infinity), and let d=n-k. Then the sorted Smith exponents of H have exactly the law
```
(a_1,...,a_k, r+e_1,...,r+e_d),
```
where (e_1,...,e_d) are the Smith exponents of a centered Haar matrix in Sym_d(Z_p). The d=0 case is deterministic. Thus two centers with the same shallow exponents have identical Smith laws regardless of the deeper entries. This strengthens the [determinant image](BSD-TAME-SYMMETRIC-DETERMINANT-ARBITRARY-RANK.md) from a range statement to a distribution statement.

## Block elimination preserves integral equivalence

Unimodular congruence preserves Haar. In the diagonalized coordinates write
```
H = [ A     p^r X         ],
    [ p^r X^t   p^r Z     ],
A = D_1 + p^r Y.
```
Here Z is symmetric Haar because the deeper diagonal B_2/p^r is integral; Z is independent of A,X. For k>0, A=D_1(I+p^r D_1^(-1)Y), with the second factor congruent to I modulo p. Thus the shallow exponents of A are exactly a_i, and A^(-1) has all its entries in p^(-a_k)Z_p. In particular A^(-1)p^r X is integral. Eliminating both cross blocks by unimodular congruence leaves A and p^r times the symmetric Schur complement Z-p^r X^t A^(-1)X. Conditioned on A,X this is a fixed integral translation of Z and has exactly the centered Haar law. With k=0 there is no elimination. The complement's exponents are all at least r, so concatenation is already sorted. This last point also excludes mixing the shallow and deep ranges.

## Exact centered recursion and determinant consequence

Set q_n(h) to the probability of nullity h for a uniform symmetric n-by-n matrix over F_p. Conditional on a specific reduction of nullity h, perform a fixed lifted congruence so that the first n-h coordinates are invertible modulo p and the remaining reduction is zero. Eliminate as above with r=1. The centered matrix then has n-h zero Smith exponents followed by 1 plus the exponents from a centered symmetric h-by-h matrix. This also works for h=n by dividing all entries by p. The process terminates almost surely: at a fixed positive size n a self-loop has probability p^(-n(n+1)/2)<1, and each non-loop decreases size.

For T_n(j)=Pr(v_p(det S_n)>=j) with T_n(j)=1 for j<=0 and T_0(j)=0 for positive j, the exact finite recurrence is
```
T_n(j) = sum_{h=0}^n q_n(h) T_h(j-h),  j>0.
```
Positive-depth calls strictly reduce the depth in every nonzero term, because the h=0 term is zero at j>0. The shifted determinant valuation is sum_i a_i+r d+v_p(det S_d). For d=2 this recovers the earlier [rank-two formula](BSD-RANK-TWO-TAME-HAAR-DET-TAIL.md); the recursion can use exact finite-field counts at any fixed rank. For a rational generating function, G_0(z)=1 and
```
G_n(z) = [sum_{h<n} q_n(h) z^h G_h(z)] / [1-p^(-n(n+1)/2) z^n].
```

## What a Frobenius test would need

On the [rank-two nested family](BSD-TAME-NESTED-CHEBOTAREV-TAIL.md), the same proof transfers to any event depending on the Smith exponents truncated at j, not just determinant divisibility: the exponents truncated at j are exactly those of the matrix over Z/p^j, as recoverable from its cokernel over that ring. The approximation errors there vanish entrywise modulo p^j for m>=j+b, and a common unit scalar leaves Smith exponents unchanged. The right-Haar averaging proof is unchanged. This uses only the same fixed rank-two hypotheses; for higher arithmetic rank it requires an analogous neighborhood, joint cochain directions and Frobenius precision control. Classical centered matrix theory supplies none of those hypotheses or the identification of a spectral family.

## Exact finite replay

Modulo p^2, independently enumerate matrices and compare the determinant counts to the recursion with exact integers. Rank up to 3 at p=3, up to 2 at p=5. This checks 15 finite equalities, not the general proof or any prime distribution.
```js
const det=A=>!A.length?1:A[0].reduce((s,x,j)=>s+(-1)**j*x*det(A.slice(1).map(r=>r.filter((_,k)=>k!==j))),0);
const rank=(A,p)=>{
 A=A.map(r=>r.map(x=>(x%p+p)%p)); let t=0;
 for(let j=0;j<A.length;j++){
  const i=A.findIndex((r,i)=>i>=t&&r[j]);if(i<0)continue;
  [A[t],A[i]]=[A[i],A[t]];
  let inv=1;while(inv*A[t][j]%p!==1)inv++;
  for(let h=t+1;h<A.length;h++){
   const a=A[h][j]*inv%p;
   for(let k=j;k<A.length;k++)A[h][k]=((A[h][k]-a*A[t][k])%p+p)%p;
  }
  t++;
 }
 return t;
};
const enumerate=(n,m,visit)=>{
 const A=Array.from({length:n},()=>Array(n).fill(0)),I=[];
 for(let i=0;i<n;i++)for(let j=i;j<n;j++)I.push([i,j]);
 const go=k=>{
  if(k===I.length){visit(A);return;}
  const [i,j]=I[k];
  for(let x=0;x<m;x++){A[i][j]=A[j][i]=x;go(k+1);}
 };
 go(0);
};
let checks=0;
for(const [p,b] of [[3,3],[5,2]]){
 const coeff=[ [1] ];
 for(let n=1;n<=b;n++){
  const C=Array(n+1).fill(0);enumerate(n,p,A=>C[n-rank(A,p)]++);coeff.push(C);
 }
 const T=(n,j)=>j<=0?1:n===0?0:coeff[n].reduce((s,c,d)=>s+c*T(d,j-d),0)/p**(n*(n+1)/2);
 const m=p*p;
 for(let n=1;n<=b;n++){
  const F=Array(3).fill(0);enumerate(n,m,A=>{const z=det(A);F.forEach((_,j)=>{F[j]+=+(z%p**j===0)});});
  const d=n*(n+1)/2;
  for(let j=0;j<=2;j++){
   // T(n,j) has denominator dividing p^(dj); powers clear it exactly.
   const N=(n,j)=>j<=0?1n:n===0?0n:coeff[n].reduce((s,c,h)=>{
    const D=n*(n+1)/2,e=h*(h+1)/2, k=Math.max(j-h,0);
    if(!c||h===0)return s;
    return s+BigInt(c)*N(h,k)*BigInt(p)**BigInt(D*(j-1)-e*k)
   },0n);
   if(BigInt(F[j])*BigInt(p)**BigInt(d*j)!==BigInt(m)**BigInt(d)*N(n,j))throw Error([p,n,j,F,T(n,j)]);
   checks++;
  }
 }
}
console.log(checks);
```
