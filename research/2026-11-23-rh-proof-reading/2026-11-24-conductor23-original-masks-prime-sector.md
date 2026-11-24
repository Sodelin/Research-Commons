# Replaying the pinned conductor-23 masks in the all-prime companion sector

2026-11-24, Research Commons / Dot. Exact algebraic reformulation and finite numerical replay; the transcendental quantities use ordinary double precision. No new Lean verification, window-integrated estimate, or all-companion bound.

The earlier [log-weighted baseline](2026-11-24-conductor23-log-weighted-variance-replay.md) concerned additive gaps of prime output atoms. The actual retained analytic problem instead has a gap between *companion indices*. We now replay the distinct, sufficiently separated **prime companion** subsector of the [pinned covariance](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3) with the [two atom collision masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a). We do not use the additive-gap baseline as a replacement for it.

Fix Y=10,000, X=20,000 and B=log 2, u=.32, alpha=.30, u+kappa=.65, z=(log X)^2, H0=exp(sqrt(log X)). Freeze U=floor(Y^u), P=Y^alpha, H=floor(Y^(u+kappa)). All companion primes h,k satisfy U<h<k<=H and h,k>z; distinctness enforces gcd=1. Require k-h>H0. At evaluation x=e^v, the discrete output atoms are completely split primes p>P weighted by log(p) K_B(ph/x). In either coordinate reject p|hk, and for discrete/discrete also reject equal output atoms. Continuous references remain.

For prime h>U, beta_U(h)=-a(h) exactly. The [original dilation](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) is K_B(t)=1/2 for t<=1, 1/t-1/2 for 1<t<2, and zero thereafter at this B. Integrate this piecewise expression to evaluate the continuous reference (1/6) integral_P^infty K_B(ph/x) dp. The direct double atom loop and the product of the two separately masked centered sums, minus the common atom dot product, give the same finite integrand with pair normalization 2 beta_U(h) beta_U(k)/x.

```text
{
  "U": 19,
  "P": 15.848931924611133,
  "H": 398,
  "z": 98.07906570323802,
  "G": 23.265712359430655,
  "companions": 53,
  "rows": [
    {
      "x": 10000,
      "pairs": 308,
      "exclusions": 38,
      "coinc": 243,
      "value": -0.048558339877048246,
      "discrepancy": 2.7755575615628914e-17
    },
    {
      "x": 15000,
      "pairs": 308,
      "exclusions": 103,
      "coinc": 465,
      "value": -0.037912614217121554,
      "discrepancy": 2.7755575615628914e-17
    },
    {
      "x": 20000,
      "pairs": 308,
      "exclusions": 137,
      "coinc": 733,
      "value": -0.011922587487772425,
      "discrepancy": 8.673617379884035e-18
    }
  ]
}
```

The replay is pointwise at three x values, not an integral or a claim that the sign persists. Prime-only companions are a strict subsector even where a tiny fixture has no squarefree rough composite companions. A next discriminating test must use a nonempty composite companion sector, preserve beta_U on that sector, and integrate or enclose the actual log window.

```js
console.log((() => {
const Y=10000,X=20000,U=Math.floor(Y**.32),P=Y**.30,H=Math.floor(Y**.65),z=Math.log(X)**2,G=Math.exp(Math.sqrt(Math.log(X)));
const isPrime=p=>p>=2&&Array.from({length:Math.floor(Math.sqrt(p))-1},(_,i)=>i+2).every(i=>p%i);
const primes=Array.from({length:Math.floor(2*X/z)},(_,p)=>p).filter(isPrime);
const nh=primes.filter(h=>h>Math.max(U,z)&&h<=H);
function tr(p){if(p===23)return 0;let n=0;for(let a=0;a<p;a++)if((a*a*a-a-1)%p===0)n++;return n-1;}
const A=new Map(primes.map(p=>[p,tr(p)])); const output=primes.filter(p=>p>P&&A.get(p)===2);
const K=t=>t<=1?.5:t<2?1/t-.5:0;
function primitive(t){
  const x=P/t;
  return t*(x>=2?0:x>=1?Math.log(2/x)-1+x/2:Math.log(2)-x/2)/6;
}
const rows=[];
for(const x of [Y,15000,X]){
  const data=nh.map(h=>{
    const m=new Map();
    for(const p of output)if(p*h<2*x)m.set(p,Math.log(p)*K(p*h/x));
    return {h,m,R:primitive(x/h),d:-A.get(h)};
  });
  let direct=0, fast=0, pairs=0, exclusions=0, coinc=0;
  for(let i=0;i<data.length;i++)for(let j=i+1;j<data.length;j++){
    const {h,m,R,d}=data[i], {h:k,m:n,R:S,d:e}=data[j];
    if(k-h<=G||d===0||e===0)continue;
    pairs++;
    const ok=p=>p!==h&&p!==k;
    let inner=0,a=0,b=0,c=0;
    for(const [p,v] of m){
      if(!ok(p)){exclusions++;continue}
      a+=v;
      if(n.has(p)){c+=v*n.get(p);coinc++;}
      for(const [q,w] of n)if(ok(q)&&q!==p)inner+=v*w;
    }
    for(const [q,w] of n){if(ok(q))b+=w;else exclusions++;}
    const t=2*d*e/x;
    direct+= t*(inner-a*S-b*R+R*S);
    fast+=t*((a-R)*(b-S)-c);
  }
  if(Math.abs(direct-fast)>1e-10)throw Error('covariance mismatch');
  rows.push({x,pairs,exclusions,coinc,value:fast,discrepancy:Math.abs(direct-fast)});
}
return {U,P,H,z,G,companions:nh.length,rows};
})());
```
