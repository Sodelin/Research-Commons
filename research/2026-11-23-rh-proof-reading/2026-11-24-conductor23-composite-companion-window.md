# A nonempty composite-companion Artin window

2026-11-24, Research Commons / Dot. Bounded numerical replay of an exact restricted sub-sum; no certified quadrature enclosure, asymptotic estimate, or Lean proof.

This follows the [prime-companion replay](2026-11-24-conductor23-original-masks-prime-sector.md). Keep the original kernel at B=log 2, exact continuous reference, prime-atom coincidence mask, squarefree and roughness conditions, coprimality, and strict companion gap. Restrict both companion indices to [47000,53500] as an additional selection. Use Y=10^6, X=2Y, u=.45, alpha=.19, u+kappa=.79, and the pinned z=(log X)^2 and H0=exp(sqrt(log X)). This is a finite window, not evidence for the asymptotic admissibility condition.

For squarefree h>U, multiplicativity gives beta_U(h)=prod_(p|h) a(p) times sum_(d|h,d>U) (-1)^omega(d). This follows from the local coefficient of 1/L at a prime, -a(p), and the squarefree divisor expansion of the convolution. The code evaluates the finite-field splitting test for a(p); ramification is outside the companion slice. Evaluate the continuous reference by integrating the piecewise K_B exactly as a function (then numerically evaluate its log); evaluate the integral in log x by ordinary composite Simpson at three resolutions. Compare independent expanded and factorized atom expressions at three sample points.

```text
{
  "U": 501,
  "H": 54954,
  "P": 13.80384264602885,
  "z": 210.5011493736387,
  "G": 45.10635745278795,
  "output": [
    59
  ],
  "nonzeroCompanions": 318,
  "composites": [
    {
      "h": 47053,
      "f": [
        211,
        223
      ],
      "coeff": 4
    },
    {
      "h": 49163,
      "f": [
        211,
        233
      ],
      "coeff": -2
    },
    {
      "h": 50429,
      "f": [
        211,
        239
      ],
      "coeff": -2
    },
    {
      "h": 51959,
      "f": [
        223,
        233
      ],
      "coeff": -2
    },
    {
      "h": 53297,
      "f": [
        223,
        239
      ],
      "coeff": -2
    }
  ],
  "pairCounts": [
    48235,
    1542,
    2
  ],
  "maxDiff": 3.469446951953614e-18,
  "I64": [
    -0.0009509568107903854,
    -0.00019124839931224807,
    0.000029842569741238962
  ],
  "I128": [
    -0.0009509816204651787,
    -0.00019124106312686204,
    0.00002984296294107288
  ],
  "I256": [
    -0.0009509789104264573,
    -0.00019124173358600974,
    0.000029842954489944805
  ]
}
```

Prime-prime and mixed contributions were negative in this sampled integral; the two composite-composite pairs had a positive total. Only one completely split output atom occurs in this fixture, so the distinct discrete/discrete output sector is empty. The divisibility masks are vacuous by the different scales (all companion prime factors exceed 210, every output prime is at most 85), checked by the replay. Thus no broader cancellation conclusion follows. A useful next fixture needs multiple output atoms and substantially more composite companions without replacing the original masks.

```js
console.log((() => {
const Y=1e6,X=2e6,U=Math.floor(Y**.45),H=Math.floor(Y**.79),P=Y**.19,z=Math.log(X)**2,G=Math.exp(Math.sqrt(Math.log(X)));
const lo=47000, hi=53500;
const prime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true;};
const mod=(a,p)=>((a%p)+p)%p;
const mul=(a,b,p)=>{
 const v=[0,0,0,0,0];
 for(let i=0;i<3;i++)for(let j=0;j<3;j++)v[i+j]+=a[i]*b[j];
 return [mod(v[0]+v[3],p),mod(v[1]+v[3]+v[4],p),mod(v[2]+v[4],p)];
};
const qr=new Set(Array.from({length:22},(_,i)=>((i+1)**2)%23));
function tr(p){
 if(!qr.has(p%23))return 0;
 let a=[1,0,0],b=[0,1,0],k=p;
 while(k){if(k%2)a=mul(a,b,p);b=mul(b,b,p);k=Math.floor(k/2);}
 return a[0]===0&&a[1]===1&&a[2]===0?2:-1;
}
const output=[];
for(let p=Math.floor(P)+1;p<=2*X/lo;p++)if(prime(p)&&tr(p)===2)output.push(p);
const companions=[];
for(let h=lo;h<=Math.min(hi,H);h++){
 if(h<=U)continue;
 let a=h,f=[];
 for(let p=2;p*p<=a;p++)if(a%p===0){a/=p;f.push(p);if(a%p===0){a=0;break;}}
 if(!a)continue;
 if(a>1)f.push(a);
 if(f.some(v=>v<=z))continue;
 let coeff=0;
 for(let m=0;m<(1<<f.length);m++){
  let d=1,s=1;
  for(let j=0;j<f.length;j++)if((m>>j)&1){d*=f[j];s=-s;}
  if(d>U)coeff+=s;
 }
 for(const p of f)coeff*=tr(p);
 if(coeff)companions.push({h,f,coeff});
}
function gcd(a,b){while(b)[a,b]=[b,a%b];return a;}
const pairs=[];
for(let i=0;i<companions.length;i++)for(let j=i+1;j<companions.length;j++){
 const a=companions[i],b=companions[j];
 if(b.h-a.h<=G||gcd(a.h,b.h)!==1)continue;
 if(output.some(p=>a.h%p===0||b.h%p===0))throw Error("non-vacuous divisor mask not implemented");
 pairs.push([i,j,a.coeff*b.coeff,a.f.length+b.f.length-2]);
}
const K=t=>t<=1?.5:t<2?1/t-.5:0;
function evalAt(x,direct=false){
 const cache=companions.map(({h})=>{
  const a=output.map(p=>Math.log(p)*K(p*h/x));
  const t=x/h,y=P/t;
  const R=t*(y>=2?0:y>=1?Math.log(2/y)-1+y/2:Math.log(2)-y/2)/6;
  return [a,a.reduce((s,v)=>s+v,0),R];
 });
 const out=[0,0,0];
 for(const [i,j,w,b] of pairs){
  const [a,A,R]=cache[i],[c,C,S]=cache[j];
  let t=0;
  if(direct){
    for(let m=0;m<a.length;m++)for(let n=0;n<c.length;n++)if(m!==n)t+=a[m]*c[n];
    t+=-A*S-C*R+R*S;
  } else {
    t=(A-R)*(C-S);
    for(let m=0;m<a.length;m++)t-=a[m]*c[m];
  }
  out[b]+=2*w*t/x;
 }
 return out;
}
let maxDiff=0;
for(const x of [Y,1.5*Y,X]){
 const a=evalAt(x),b=evalAt(x,true);
 maxDiff=Math.max(maxDiff,...a.map((v,i)=>Math.abs(v-b[i])));
}
if(maxDiff>1e-11)throw Error("pointwise mismatch");
function integrate(n){
 const s=[0,0,0],dv=Math.log(X/Y)/n;
 for(let j=0;j<=n;j++){
  const f=evalAt(Y*Math.exp(j*dv));
  const w=j===0||j===n?1:j%2?4:2;
  for(let k=0;k<3;k++)s[k]+=w*f[k];
 }
 return s.map(v=>v*dv/3);
}
return {U,H,P,z,G,output,nonzeroCompanions:companions.length,composites:companions.filter(a=>a.f.length>1),
  pairCounts:[0,1,2].map(b=>pairs.filter(p=>p[3]===b).length),maxDiff,I64:integrate(64),I128:integrate(128),I256:integrate(256)};
})());
```
