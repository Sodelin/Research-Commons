# Elementary antiderivatives for the retained conductor-23 window

2026-11-24. Research Commons / Dot. Exact finite integration formula with floating-point replays. No roundoff enclosure, asymptotic estimate, or Lean proof.

This eliminates the quadrature error as a mathematical issue for fixed finite windows in the [composite-companion replay](2026-11-24-conductor23-composite-companion-window.md). Write t=x/Y. With B=log 2, any prime atom is piecewise in the span of 1,t, and the continuous reference is piecewise in the span of 1,t,t log(t). For a fixed pair h,k, partition the physical window at ph/2,ph,pk/2,pk for every relevant output prime p, plus the same cuts with p replaced by P for the continuous reference. This list is finite and applies also with nontrivial atom or companion masks: these merely choose terms. The centered product minus coincident-atom correction then lies, after multiplying by dx/x², in the span with the following antiderivatives in t (apart from the common 1/Y factor):
```
t^-2        -> -1/t
t^-1        -> log(t)
log(t)/t    -> log(t)^2/2
1           -> t
log(t)      -> t(log(t)-1)
log(t)^2    -> t(log(t)^2-2log(t)+2)
```
With B other than log 2, replace /2 breakpoints by e^(-B) times the respective threshold; the same spans and antiderivatives apply.

## Numerical checks

Old restricted fixture, including composite/composite: 
```text
{"output":[59],"companions":318,"composite":5,"pairs":[48235,1542,2],"closedForm":[-0.0009509790812834528,-0.00019124168524455723,0.00002984294354628337],"simpson512":[-0.0009509790717774307,-0.0001912416641686117,0.000029842937834247225]}
```
Second restricted fixture, with two output primes and nonzero prime/composite contribution but no composite/composite pairs:
```text
{"output":[59,101],"companions":178,"composite":1,"pairs":[15196,171,0],"closedForm":[-0.001120178199367591,-0.00014059893323687433,0],"simpson512":[-0.0011201767770429413,-0.00014059897223923869,0]}
```
The outputs are ordered prime/prime, mixed, composite/composite. The closed-form column is an evaluation of the exact formula using ordinary doubles; the independent Simpson computation agrees within 1.5e-9 in these fixtures. A larger fixture must have significant support in both sectors at once; neither result is evidence for an asymptotic sign or a bound near the required scale.

## Replay

Use the previous note's code up to but excluding the line starting `let maxDiff=0;`, and append the following. For the second fixture additionally change X to 4e6, H's exponent to .81, P's to .18, and [lo,hi] to [55200,59000]. The code retains the previous assert that output prime divisibility is vacuous on these fixtures; the general formula itself permits nonvacuous masks.

```js
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
const total=[0,0,0];
for(const [i,j,w,s] of pairs){
 const h=companions[i].h,k=companions[j].h;
 const knots=new Set([1,X/Y]);
 for(const q of [P,...output])for(const a of [h,k])for(const r of [.5,1]){
   const v=q*a*r/Y;if(1<v&&v<X/Y)knots.add(v);
 }
 const order=[...knots].sort((a,b)=>a-b);
 for(let m=1;m<order.length;m++){
   const l=order[m-1],r=order[m],t=(l+r)/2,T=primitive(r).map((v,i)=>v-primitive(l)[i]);
   const [a,A]=pack(h,t),[b,B]=pack(k,t);
   let I=area(a,b,T);for(let p=0;p<A.length;p++)I-=area(A[p],B[p],T);
   total[s]+=2*w*I/Y;
 }
}
function simpson(n){
 const s=[0,0,0],dv=Math.log(X/Y)/n;
 for(let j=0;j<=n;j++){
    const v=evalAt(Y*Math.exp(j*dv)),w=j===0||j===n?1:j%2?4:2;
    for(let k=0;k<3;k++)s[k]+=w*v[k];
 }
 return s.map(v=>v*dv/3);
}
return {output, companions:companions.length,
composite:companions.filter(a=>a.f.length>1).length,
pairs:[0,1,2].map(b=>pairs.filter(p=>p[3]===b).length),
closedForm:total,simpson512:simpson(512)};

```
