# Exact replay of the incidence-width rank transitions

2026-11-25 UTC. Research Commons / Dot. Reproducible finite check for the nice-decomposition invariant in the [incidence-width hand proof](EXACT-RANK-INCIDENCE-FOREST.md), motivated by independent checks from background research. No Lean verification or production tree-decomposition solver.

This replay builds actual nice-decomposition operations on two branches with a shared bag: introduce vertices, introduce each signed edge once, forget branch-private vertices, join, and finish at an empty root. Its random fixture generator assigns each vertex to the shared bag or to one branch. It never generates an edge between the two private parts; an edge with both endpoints shared is allocated to exactly one branch. Each vertex's bags are connected, every incidence edge is covered, and all labeled clauses, including isolated or repeated labels, remain in the input. The shape has one join, not an arbitrary tree of joins. Bags are stored by the original bit positions because all fixtures are small.

Weighted projected counting here charges a forgotten clause once. At a join shared variables must agree while the two flags for a shared clause are ORed. Multiple different witness rows are unioned into a *single* feasible row set for a fixed combined selection before its weight is accumulated. In particular a shared clause whose literals are divided across branches need not be true in both. All 600 weighted fixtures matched complete enumeration of clause subsets and assignments, including 249 with at least one shared clause having incident literals in both children. Arithmetic on counts uses BigInt.

Standalone JavaScript, replacing text by console.log in Node:

```javascript
function test(n,F,W,core,priv,edges){
  const m=F.length, empty={b:0,E:[[0,[0],1n]]};
  const bit=i=>1<<i, vm=(1<<n)-1;
  function build(b,feed){
    const map=new Map();
    const emit=(S,A,w)=>{
      if(!A.length||!w)return;
      A=[...new Set(A)].sort((x,y)=>x-y);
      const k=S+':'+A;
      if(map.has(k))map.get(k)[2]+=w;else map.set(k,[S,A,w]);
    };
    feed(emit);return {b,E:[...map.values()]};
  }
  function introduce(D,i){
    const b=bit(i);
    return build(D.b|b,e=>{for(const [S,A,w] of D.E)
      if(i<n)e(S,A.concat(A.map(x=>x|b)),w);
      else {e(S,A,w);e(S|b,A,w);}
    });
  }
  function edge(D,j,l){
    const vb=bit(Math.abs(l)-1),cb=bit(n+j);
    if(!(D.b&vb)||!(D.b&cb))throw Error('missing edge endpoint');
    return build(D.b,e=>{for(const [S,A,w] of D.E)
      e(S,A.map(x=>Boolean(x&vb)===(l>0)?x|cb:x),w);
    });
  }
  function forget(D,i){
    const b=bit(i), mask=~b;
    return build(D.b&mask,e=>{for(const [S,A,w] of D.E){
      if(i<n)e(S,A.map(x=>x&mask),w);
      else {
        const take=Boolean(S&b);
        e(S&mask,A.filter(x=>!take||x&b).map(x=>x&mask),w*W[i-n][+take]);
      }
    }});
  }
  function join(L,R){
    if(L.b!==R.b)throw Error('different bags');
    return build(L.b,e=>{for(const [s,A,a] of L.E)for(const [t,B,b] of R.E){
      if(s!==t)continue;
      const C=[];for(const x of A)for(const y of B)if(!((x^y)&vm))C.push(x|y);
      e(s,C,a*b);
    }});
  }
  function branch(i){
    let D=empty;
    for(const t of core.concat(priv[i]))D=introduce(D,t);
    for(const [j,l] of edges[i])D=edge(D,j,l);
    for(const t of priv[i])D=forget(D,t);
    return D;
  }
  let D=join(branch(0),branch(1));
  for(const t of core)D=forget(D,t);
  const got=D.E.reduce((a,x)=>a+x[2],0n);
  let expect=0n;
  for(let S=0;S<1<<m;S++){
    let ok=false;
    for(let x=0;x<1<<n&&!ok;x++)ok=F.every((C,j)=>!(S&bit(j))||C.some(l=>Boolean(x&bit(Math.abs(l)-1))===(l>0)));
    if(ok)expect+=W.reduce((p,a,j)=>p*a[+(Boolean(S&bit(j)))],1n);
  }
  if(got!==expect)throw Error(JSON.stringify({n,F,core,priv,edges}));
}
let seed=150795;
const rnd=n=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)>>>8)%n;
let split=0, counts=0;
for(let z=0;z<600;z++){
 const n=1+rnd(5),m=1+rnd(7),kind=Array.from({length:n+m},()=>rnd(3));
 const K=[],P=[[],[]],E=[[],[]],F=Array.from({length:m},()=>[]);
 kind.forEach((k,i)=>k===0?K.push(i):P[k-1].push(i));
 let crosses=false;
 for(let j=0;j<m;j++){
   let used=0;
   for(let i=0;i<n;i++){
     let a=kind[i],b=kind[n+j];
     if(a&&b&&a!==b||rnd(3)===0)continue;
     const side=(a||b||1+rnd(2))-1,l=(1+i)*(rnd(2)?1:-1);
     E[side].push([j,l]); F[j].push(l); used|=1<<side;
   }
   if(used===3)crosses=true;
 }
 const W=F.map(()=>[BigInt(rnd(4)),BigInt(rnd(4))]);
 test(n,F,W,K,P,E); counts++; if(crosses)split++;
}
text({counts,split});
```
