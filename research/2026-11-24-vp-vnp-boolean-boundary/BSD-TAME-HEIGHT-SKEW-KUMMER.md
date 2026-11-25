# The skew part of the corrected tame height is fixed Kummer data

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof at the cochain stage of the [rank-one source, section 5](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex), with exact finite-field checks of the matrix identity. It addresses the symmetry hypothesis of the [arbitrary-rank determinant-image result](BSD-TAME-SYMMETRIC-DETERMINANT-ARBITRARY-RANK.md). It does not identify a higher-rank spectral leading value or have Lean verification.

Fix the rational points and rational Poincaré lifts in the [joint Kummer construction](BSD-RANK-TWO-TAME-COMMUTATOR-FREEDOM.md). Use compatible Tate splittings so that the polarization cochain for argument j acts by pairing with the same Kummer representative x_j used in the other argument (a common sign is absorbed into the alternating Tate pairing e). The rank-one construction describes this normalization: splittings of the Tate extension correspond to division points of the polarized point, hence may be taken from the polarized Kummer choices. Let k_ij be the corresponding scalar cochain, so for the inhomogeneous differential and the usual left action

    d k_ij(g,h) = -c_ij(g,h),
    c_ij(g,h) = e(x_j(g), g x_i(h)).

Take a fixed common finite set S containing p and all bad, nonintegral and ramified primes of the data. These cochains factor through the Galois group unramified outside S: the extensions and point and lift division torsors extend away from S, where p is invertible and division is étale. One may instead impose this as an explicit cochain hypothesis. Choices differing by a fixed coboundary are allowed in the scalar calculation below.

## A scalar cocycle, not a new skew height direction

Set q_ij(g)=e(x_j(g),x_i(g)). The ordinary cocycle law for the x_i, equivariance of e and its alternating sign give

    d q_ij(g,h)
      = -e(x_j(g), g x_i(h))-e(g x_j(h),x_i(g))
      = -c_ij(g,h)+c_ji(g,h).

Thus z_ij=k_ij-k_ji-q_ij is a 1-cocycle with values in Q_p(1), unramified outside S. Over Q its cohomology class is a rational p-adic linear combination of the Kummer classes of the primes in S. In detail, after clearing a fixed p-power denominator, at each level finite Kummer theory identifies a class with a rational number modulo p^m-th powers. For a prime outside S the valuation of this rational representative is zero modulo p^m, since the class is unramified there and the prime is different from p. The sign contributes no odd-p class, and compatibility of the valuation coordinates over m gives the S-prime generators after passage to the limit. Consequently killing all p-power radicals of the finitely many S-primes and all p-power roots of unity kills z_ij itself on that subgroup: it kills the chosen ordinary Kummer representatives, and any remaining coboundary there is zero by trivial action on Q_p(1). The same fixed set works for all pairs of any fixed finite list of points.

## The inverse correction has exactly this skew part

Let T be the Tate matrix at g, with T-I invertible, and define A=T(T-I)^(-1). Write star for the adjoint with respect to e. In dimension two T* = det(T) T^(-1). For delta=det(T), a direct identity of commuting matrices gives

    A + A* - I = (delta-1) T (T-I)^(-1) (delta I-T)^(-1).

Indeed the left side is (T-I)^(-1)+delta(delta I-T)^(-1). At determinant one this gives A + A* = I. By alternation,

    e(x_j(g), A x_i(g)) - e(x_i(g), A x_j(g))
      = e(x_j(g), (A + A*) x_i(g)) = q_ij(g).

The source's corrected array H_ij=k_ij-e(x_j,A x_i) therefore has skew part exactly z_ij(g) at determinant one. In particular it is symmetric at the limiting g in the fixed radical-and-cyclotomic kernel. This uses the fixed scalar Kummer data, not invariance under transposing just one unrelated choice of cochain.

At finite precision, if det(T)=1 modulo p^m and (T-I)^(-1) has entries of valuation at least -s in a symplectic integral basis, then (delta I-T)^(-1)=T^(-1)(T*-I)^(-1) has the same bound since T is integral invertible and star preserves the lattice. The correction error has valuation at least m-2s for integral x_i(g). If g also fixes the matching p^m-th radicals of the S-primes, the representative z_ij(g) is zero modulo p^(m-b) for some fixed b accounting for the rational class coefficients and the scalar coboundary. Thus the skew part tends to zero uniformly with this normalization (additional fixed denominators of the data can be absorbed in b).

## Consequence and limit

Under the joint Kummer and eligible lift hypotheses already in the commutator note, adjoining these fixed radical conditions does not remove the commutators used to vary the symmetric entries. At determinant one the initial corrected array is now symmetric, not just its increments. After a common denominator clearing, the symmetric determinant-image classification applies to that actual normalized cochain coset. This removes the previous *cochain symmetry* assumption under the stated compatible splittings and finite ramification; it does not produce the rank-two spectral map or the arithmetic calibration to a leading L-value.

## Exact matrix replay

All eligible 2-by-2 matrices over the four small fields were examined: 13,970 checks, including 1,596 at determinant one. This does not test global Galois classes. Standalone JavaScript (replace text by console.log).

```javascript
const mul=(A,B,p)=>A.map(r=>B[0].map((_,j)=>r.reduce((s,x,i)=>s+x*B[i][j],0)%p));
const norm=(x,p)=>(x%p+p)%p;
const det=(A,p)=>norm(A[0][0]*A[1][1]-A[0][1]*A[1][0],p);
const I=[[1,0],[0,1]],sub=(A,B,p)=>A.map((r,i)=>r.map((x,j)=>norm(x-B[i][j],p)));
const scale=(x,A,p)=>A.map(r=>r.map(y=>norm(x*y,p)));
const adj=A=>[[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]];
const inv=(A,p)=>{const d=det(A,p);if(!d)return null;let u=1;while(d*u%p!==1)u++;return scale(u,adj(A),p)};
let checked=0,detOne=0;
for(const p of [3,5,7,11])for(let t=0;t<p**4;t++){
 let u=t;const T=I.map(r=>r.map(()=>{const z=u%p;u=Math.floor(u/p);return z;}));
 const delta=det(T,p),D=sub(T,I,p),F=sub(scale(delta,I,p),T,p),Di=inv(D,p),Fi=inv(F,p);
 if(!delta||!Di||!Fi)continue;
 const A=mul(T,Di,p),diff=A.map((r,i)=>r.map((x,j)=>norm(x+adj(A)[i][j]-I[i][j],p)));
 const rhs=scale(delta-1,mul(T,mul(Di,Fi,p),p),p);
 if(JSON.stringify(diff)!==JSON.stringify(rhs))throw Error("matrix identity");
 checked++;if(delta===1)detOne++;
}
text({checked,detOne});
```
