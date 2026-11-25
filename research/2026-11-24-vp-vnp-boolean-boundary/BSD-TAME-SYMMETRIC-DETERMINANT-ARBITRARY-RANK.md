# Exact determinant images for symmetric tame-height cosets in every rank

2026-11-25 UTC. Research Commons / Dot. Scoped hand algebra with exact modular replay. The result is conditional on the indicated commutator and symmetry hypotheses when interpreted as a height statement. It does not give a leading L-value formula, identify the actual spectral object, or have Lean verification.

The [rank-two determinant image](BSD-RANK-TWO-TAME-DETERMINANT-IMAGE.md) did not require symmetry of the initial matrix. In every size n≥1 there is an exact classification with a symmetric initial matrix. Fix an odd prime p, a scale r≥0, and an integral symmetric matrix B. Diagonalize B by a congruence over GL_n(Z_p); write the valuations of the diagonal entries as lambda_1≤...≤lambda_n, assigning infinity to zero. Let k be the number strictly less than r and L=sum_(i≤k) lambda_i. The exact image of det on B+p^r Sym_n(Z_p) is

    p^(L+r(n−k)) Z_p,                    k<n;
    det(B)+p^(L+r−lambda_n) Z_p,         k=n.

Thus if even one diagonal direction is divisible by p^r in an integral diagonalization, the determinant ranges over a full ideal, with all consecutive sufficiently large valuations attained. If every direction is below the commutator scale, no determinant valuation can change at all. This distinguishes a genuine valuation obstruction from a coset on which parity is constant.

## Proof

Diagonalization is elementary at odd p. Pick a nonzero entry of smallest valuation in the current matrix. If only an off-diagonal entry attains that valuation, some vector e_i+e_j has quadratic value of that valuation, since 2 is invertible and the two diagonal entries have greater valuation. That primitive vector can be made a first basis vector. Orthogonalize the remaining vectors by integral multiples of the first, since its value divides the other entries; continue on the complement, leaving zeros if the matrix becomes zero. Sort the diagonal. Congruence sends the symmetric shift space onto itself and multiplies determinants by the square of a unit, which preserves the stated ideal or coset after undoing the base determinant.

For k<n, split the diagonal into the first k entries and the rest, and write an arbitrary perturbed matrix in blocks. Its leading block A is the first diagonal block D_1 plus p^r S_1. When k>0 the matrix I+p^r D_1^(-1)S_1 is congruent to I modulo p, so v(det A)=L and all entries of A^(-1) belong to p^(−lambda_k) Z_p. The off-diagonal block is p^r X. The bottom block is divisible by p^r, and the Schur correction p^(2r) X^T A^(-1) X is also divisible by p^r. The determinant is thus in the stated ideal by the block determinant identity. For k=0 the whole matrix is divisible by p^r and this containment is immediate. To reach the entire ideal take the off-diagonal block zero, leave the first k entries unchanged, and choose the last n−k diagonal entries to be p^r times (t,1,...,1) with t arbitrary in Z_p. These are all allowed because the original last entries are divisible by p^r.

For k=n, factor B out after diagonalization. The multiplier I+p^r B^(-1) S is congruent to I modulo p^(r−lambda_n). This bounds the determinant difference by the stated valuation. Varying only the diagonal entry of valuation lambda_n gives every value in the coset, because its cofactor has valuation L−lambda_n. In particular v(det B)=L< L+r−lambda_n. This proves both cases.

## What transfers to the cochains, and what does not

Under the same fixed-data and non-CM hypotheses as the [joint Kummer commutator note](BSD-RANK-TWO-TAME-COMMUTATOR-FREEDOM.md), the rational-span argument works for any fixed list of n independent rational points: stability under the full span of matrices on the Tate plane would otherwise give a nonzero scalar linear combination of the n Kummer classes vanishing on the chosen radical-and-Tate kernel. The same cyclotomic-quotient and central-homothety arguments would make that class a coboundary. The joint Kummer values therefore contain a common p-power multiple of the full product lattice. Choosing inputs supported in one pair of coordinates at a time generates each of the n diagonal and n(n−1)/2 symmetric off-diagonal matrix units using the same polarization formula; products of these commutators add the increments. This establishes a symmetric shift coset at the cochain stage, but does not itself establish symmetry of the initial corrected array. The determinant-image classification above applies when that array is symmetric in the chosen normalization (and integral after a common denominator clearing if needed). Without symmetry, one still has the uniform existence of a determinant of valuation at most nr: take the mixed finite difference over the 2^n choices of diagonal shift coordinates in {0,1}. This difference of determinant values is exactly p^(nr) by the top multiaffine coefficient, so not all values can have larger valuation.

With one fixed inverse-denominator bound p^s for the Tate block, the resolvent argument from rank two gives entry precision p^(m−2s) and a common denominator at most p^s for each corrected array. Multilinearity then gives determinant precision p^(m−(n+1)s) by replacing its rows one at a time. A chosen finite determinant valuation v is therefore preserved at m>s and m>(n+1)s+v, provided the n² compatible finite Frobenius lifts and their common normalization are realized as in the entrywise construction of [the source §5](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex). This says nothing about how to compare those directions to a spectral leading coefficient.

## Exact modular replay

Standalone JavaScript (replace text by console.log) for 54 symmetric integer fixtures in sizes 1–3. It uses congruences by integral unipotent triangular changes of basis before enumerating all image residues modulo 9. The replay is finite; the proof supplies full p-adic equality.

```javascript
const p=3,M=9;
const norm=(x,m)=>((x%m)+m)%m;
const det=A=>A.length===0?1:A[0].reduce((s,x,j)=>s+(-1)**j*x*det(A.slice(1).map(r=>r.filter((_,k)=>k!==j))),0);
let tests=0;
for(const n of [1,2,3])for(const r of [0,1,2])for(let f=0;f<6;f++){
 const P=p**r, lam=Array.from({length:n},(_,i)=>(i+f)%(r+2)).sort((a,b)=>a-b);
 if(f===5)lam[n-1]=Infinity;
 const e=lam.filter(x=>x<r),d=lam.map((x,i)=>Number.isFinite(x)?(-1)**(i+f)*p**x:0);
 const U=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?1:i<j?(f+i+j)%3-1:0));
 const B=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>d.reduce((s,x,k)=>s+x*U[k][i]*U[k][j],0)));
 const s=e.reduce((a,b)=>a+b,0);
 const exp=e.length<n?s+r*(n-e.length):s+r-e.at(-1);
 const shift=e.length<n?0:det(B), observed=new Set();
 const entries=[];for(let i=0;i<n;i++)for(let j=i;j<n;j++)entries.push([i,j]);
 const A=B.map(r=>r.slice());
 function go(k){
   if(k===entries.length){observed.add(norm(det(A),M));return;}
   const [i,j]=entries[k];
   for(let x=0;x<M/P||x===0;x++){A[i][j]=A[j][i]=B[i][j]+P*x;go(k+1);}
 }
 go(0);
 const step=p**Math.min(exp,2);
 if(observed.size!==M/step||[...observed].some(x=>norm(x-shift,step)))throw Error([n,r,f,exp]);
 tests++;
}
text(tests);
```
