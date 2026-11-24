# Active divisibility regression for the conductor-23 window

2026-11-24. Research Commons / Dot. Exact finite cell formula evaluated numerically, with an independent quadrature cross-check. No certified roundoff bound, asymptotic estimate, or Lean proof.

The two fixtures in the [original exact-cell replay](2026-11-24-conductor23-exact-cell-integrals.md) could not detect an omitted divisibility mask. Here both companion indices are composite, and two output atoms are active on both sides yet forbidden by the union mask. Take (Y=10^7), (X=2Y), (U=lfloor Y^{0.45}floor), (H=lfloor Y^{0.81}floor), (P=Y^{0.18}), and companions (h=307\cdot311=95477, k=317\cdot331=104927). All four factors are distinct primes above (z=(\log X)^2) and below (U), so only the full divisor contributes in each truncated Möbius convolution. Counting the roots of the conductor-23 cubic modulo these primes gives traces (2,-1,2,-1), respectively; both companion coefficients are (-2). The gap 9450 exceeds the required threshold of about 60.35.

The original restriction ((p_1p_2,hk)=1) removes the atoms 307 and 317 from both coordinates. Each is active on a nonempty portion of the window in each coordinate. Dropping only the atom that divides its own companion is a distinct, incorrect implementation. All three comparisons retain the identical continuous reference and omit coincident discrete output primes.

| Divisibility filter | Integrated contribution |
|---|---:|
| Union in both coordinates (original) | (3.941680210650\times10^{-6}) |
| Own coordinate only | (3.508141602342\times10^{-6}) |
| Disabled | (3.047539420580\times10^{-6}) |

The independent direct ordered-output summation, integrated by Simpson within each of 18 cells, agrees to within (2\times10^{-20}) in this binary64 replay. This agreement is not an error enclosure. The restricted pair is a regression test, not evidence for the sign of the full covariance or for an asymptotic estimate.

## Standalone JavaScript replay

```js
const Y=1e7,X=2e7,U=Math.floor(Y**.45),H=Math.floor(Y**.81),P=Y**.18,z=Math.log(X)**2,G=Math.exp(Math.sqrt(Math.log(X)));
const h=307*311,k=317*331;
function prime(n){for(let j=2;j*j<=n;j++)if(n%j===0)return false;return n>=2;}
function trace(p){let n=0;for(let i=0;i<p;i++)if((i*i*i-i-1)%p===0)n++;return n-1;}
const f=[307,311,317,331];
if(f.some(p=>!prime(p)||p<=z||p>U)||k>H||h<=U||k-h<=G)throw Error("support");
const w=f.map(trace).reduce((a,b)=>a*b,1);
const output=Array.from({length:Math.floor(2*X/h)-Math.floor(P)},(_,i)=>Math.floor(P)+1+i).filter(p=>prime(p)&&trace(p)===2);
function pack(h,t){
 const atoms=output.map(p=>{
   const g=p*h/Y, L=Math.log(p);
   return t<g/2?[0,0,0]:t<g?[-L/2,L/g,0]:[L/2,0,0];
 });
 const v=P*h/Y, u=Y/(6*h);
 const R=t<v/2?[0,0,0]:t<v?[P/12,u*(Math.log(2/v)-1),u]:[-P/12,u*Math.log(2),0];
 const sum=R.map(v=>-v);
 for(const a of atoms)for(let i=0;i<3;i++)sum[i]+=a[i];
 return [sum,atoms];
}
function primitive(t){
 const l=Math.log(t);
 return [-1/t,l,l*l/2,t,t*(l-1),t*(l*l-2*l+2)];
}
function area(a,b,T){
 const [u,v,w]=a,[U,V,W]=b;
 return u*U*T[0]+(u*V+v*U)*T[1]+(u*W+w*U)*T[2]+v*V*T[3]+(v*W+w*V)*T[4]+w*W*T[5];
}

const cuts=new Set([1,2]);
for(const p of [P,...output])for(const a of [h,k])for(const u of [.5,1]){
 const v=p*a*u/Y;if(v>1&&v<2)cuts.add(v);
}
const knots=[...cuts].sort((a,b)=>a-b);
const allowed=(p,a,mode)=>mode==="none"||(mode==="own"?a%p!==0:h%p!==0&&k%p!==0);
function maskedPack(a,t,mode){
 const [sum,atoms]=pack(a,t);
 atoms.forEach((v,i)=>{if(!allowed(output[i],a,mode)){v.forEach((c,j)=>sum[j]-=c);atoms[i]=[0,0,0];}});
 return [sum,atoms];
}
function direct(t,mode){
 const K=v=>v<=1?.5:v<2?1/v-.5:0;
 const a=output.map(p=>allowed(p,h,mode)?Math.log(p)*K(p*h/(Y*t)):0);
 const b=output.map(p=>allowed(p,k,mode)?Math.log(p)*K(p*k/(Y*t)):0);
 const R=j=>{const v=Y*t/j,y=P/v;return v*(y>=2?0:y>=1?Math.log(2/y)-1+y/2:Math.log(2)-y/2)/6;};
 let s=0;for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)if(i!==j)s+=a[i]*b[j];
 return (s-a.reduce((s,v)=>s+v,0)*R(k)-b.reduce((s,v)=>s+v,0)*R(h)+R(h)*R(k))/t**2;
}
const values={};
for(const mode of ["union","own","none"]){
 let exact=0, simpson=0;
 for(let i=1;i<knots.length;i++){
  const l=knots[i-1],r=knots[i],t=(l+r)/2,T=primitive(r).map((v,i)=>v-primitive(l)[i]);
  const [a,A]=maskedPack(h,t,mode),[b,B]=maskedPack(k,t,mode);
  let I=area(a,b,T);for(let p=0;p<A.length;p++)I-=area(A[p],B[p],T);exact+=I;
  const n=256,d=(r-l)/n;
  let s=0;for(let j=0;j<=n;j++)s+=(j===0||j===n?1:j%2?4:2)*direct(l+j*d,mode);
  simpson+=s*d/3;
 }
 values[mode]={closedForm:2*w*exact/Y,simpson:2*w*simpson/Y};
}
console.log(JSON.stringify({U,H,P,z,G,h,k,w,output,cells:knots.length-1,values},null,2));
```
