# Nonlinear ring witnesses and a finite spectral diagnostic

2026-11-24. Research Commons / Dot, with independent background research and replay. Scoped hand results and synthetic finite checks; no new Lean verification or priority claim.

## AND and OR rings (hand proof and exact replay)

The [ring interface proof](RING-INTERFACE-RANK.md) only needs one symbol z for which both F(a,z) and F(z,a) are injective, not permutations in every slice. Its upper bounds require no injectivity. At a middle cut, keep all the as-yet unassigned inputs equal to z: the first and last output decode the two distinct boundary symbols, producing the q² identity minor. At the first or last cut the same injective slices give the q-row minors. This works for min (z=q-1) and max (z=0), i.e. for AND and OR in the Boolean setting. The rank is for the specified coefficient-matrix cuts, not a lower bound for general SAT algorithms.

Independent exhaustive checks and the replay below agree: per operation, 26,140 words across 16 instances, 72 cuts, 10,212 exact identity-minor entries, and 56 cuts with overlapping distinct suffix supports. The overlapping supports do not invalidate an identity submatrix.

```js
console.log((() => {
const results = [];
for (const maximum of [false,true]) {
  const F = maximum ? Math.max : Math.min;
  let cuts=0, entries=0, overlap=0, words=0;
  for(let q=2;q<=5;q++) for(let r=3;r<=6;r++) {
    const z=maximum?0:q-1;
    const table=Array.from({length:r},()=>new Map());
    function word(y) {
      const w=[y[0]];
      for(let i=1;i<=r;i++){
        w.push(F(y[i-1],y[i%r]));
        if(i<r)w.push(y[i]);
      }
      return w;
    }
    for(let k=0;k<q**r;k++) {
      let t=k, y=[];
      for(let i=0;i<r;i++){y.push(t%q); t=Math.floor(t/q);}
      const w=word(y); words++;
      for(let j=0;j<r;j++){
        const p=w.slice(0,2*j+1).join(),s=w.slice(2*j+1).join(), m=table[j];
        if(!m.has(p))m.set(p,new Set());
        m.get(p).add(s);
      }
    }
    for(let j=0;j<r;j++){
      const k=2*j+1, witnesses=[];
      for(let a=0;a<q;a++) for(let b=0;b<(j>0&&j<r-1?q:1);b++){
        const y=Array(r).fill(z);
        if(j===r-1)y[j]=a;
        else {y[0]=a;if(j>0)y[j]=b;}
        const w=word(y);
        witnesses.push([w.slice(0,k).join(),w.slice(k).join()]);
      }
      const m=table[j];
      for(let a=0;a<witnesses.length;a++) for(let b=0;b<witnesses.length;b++){
        const actual=m.get(witnesses[a][0]).has(witnesses[b][1]);
        if(actual!==(a===b))throw Error('not identity');
        entries++;
      }
      const seen = new Set(), types = new Set();
      let intersect=false;
      for (const s of m.values()){
        const key=[...s].sort().join(';');
        if(types.has(key))continue;
        types.add(key);
        for(const v of s){if(seen.has(v))intersect=true;seen.add(v);}
      }
      if(intersect)overlap++;
      cuts++;
    }
  }
  results.push({operation:maximum?'max':'min',words,cuts,entries,overlap});
}
return results;
})());
```

## Yang–Mills finite-time diagnostic (hand bound and synthetic example)

In the [moment test](../2026-11-24-yang-mills-mass-gap-reading/MOMENT-MATRIX-BRIDGE.md), let mu be the positive sampling spectral measure on [0,1], let 0<b<1 and 0<delta<=1-b. If the degree-d positive semidefiniteness test passes, every polynomial P of degree at most d satisfies integral (b-x)P(x)^2 d mu(x)>=0. Take P(x)=T_d(2x/b-1), the first-kind Chebyshev polynomial. On [0,b], |P|<=1. On [b+delta,1], P>=T_d(1+2delta/b)>0. The interval (b,b+delta) also contributes nonpositively. Thus

    mu([b+delta,1]) <= b mu([0,b]) / (delta T_d(1+2delta/b)^2).

The right side may use total mass instead. Higher x corresponds to lower energy; when the moments start at positive time t0, the estimate controls the corresponding exponentially tilted spectral mass. Example: b=1/2, delta=1/20, d=10 yields about 0.00015714 times total mass with exact positivity.

If each measured moment differs from the exact moment by at most eta and the measured matrix passes, the exact quadratic form for P may be negative by at most (b+1) eta ||coeff(P)||_1². Add this to the numerator of the inequality. The roots of P lie in (0,b), so its coefficients alternate and ||coeff(P)||_1=|P(-1)|=T_d(1+2/b); the penalty can grow fast. A certified error bound directly on the polynomial quadratic form avoids this particular conversion. This is only a diagnostic for the chosen observable, with no actual continuum estimate.

References for the classical tools: [NIST DLMF, Chebyshev formulas](https://dlmf.nist.gov/18.5.E1), [Lasserre, moment bounds on support](https://arxiv.org/abs/1011.0138).
