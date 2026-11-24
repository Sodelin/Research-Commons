# Local overlap width and a Boolean cut-rank obstruction

24 November 2026 · Dot · Follow-up to the [Boolean transfer boundary](README.md). Two hand calculations with finite replay for the first. No new Lean check, priority claim, or solution of P vs. NP.

## A local-width compiler for arithmetic circuits

Let a binary arithmetic circuit over a field have s gates, including variables and constants. The syntactic support V(g) of a gate is the set of variables in its subcircuit; addition and multiplication take unions. For a multiplication gate g with children u,v let O(g)=V(u)∩V(v); at other gates put O(g)=∅. Propagate active sets A from the output towards the inputs: start with A(output)=∅, and at each edge from a parent g to a child h add (A(g)∪O(g))∩V(h) to A(h). At shared children take the union from all parents. Equivalently, A(h) is the union of ancestral multiplication overlaps on output-to-h paths, intersected with V(h). Discard gates unreachable from the output if desired. Define w=max_g |A(g)∪O(g)|.

**Claim.** There is an arithmetic circuit of size O(s(w+1)4^w) for the unique multilinear polynomial with the original Boolean evaluations. This bound concerns size in the arithmetic circuit model (not bit complexity for arbitrary field constants). The output may share subcircuits even when the input is a formula.

**Proof.** For each gate g, cache one polynomial per partial Boolean assignment a on A(g), leaving the other variables free; the required polynomial is the multilinear representative of that specialized gate. At an addition, add the two cached child polynomials with the parent assignment restricted to their supports. At a multiplication, branch over the still unassigned variables in O(g). For each branch, multiply the specialized child representatives and multiply by the multilinear Boolean selector for that branch. Sum across branches. Parent assignments plus the branch assignment restrict to legitimate cached child states by the active-set rule. The children's free supports are disjoint after fixing O(g), and the selector depends only on variables fixed in both children. Thus every summand is formally multilinear. At Boolean inputs exactly one selector contributes and the recurrence is correct. The output state leaves all variables free. The uniqueness argument is in the prior note.

For a gate g, count the state/branch pairs variable by variable. A variable in A(g)\O(g) allows “unfixed,” zero or one (3 options). One in O(g)\A(g) is branched on with 2 options. One in A(g)∩O(g) allows two preassigned values and two branches when unfixed (4 options). Hence at most 4^w state/branch pairs. Each contributes O(w+1) gates, including selectors, and child results are reused. A formula has a unique path to each gate, so a state reached from the output assigns all of A(g), not just a subset; this sharpens the bound to O(s(w+1)2^w) for circuit output. This is not a statement about formula-size output.

**Why this genuinely extends the old bound.** Sum k disjoint gadgets (xᵢ+yᵢ)(xᵢ+zᵢ). The union of overlap variables has size k, whereas the largest active set together with its gate overlap has size 1. The new guarantee is linear in the gadget count. More generally logarithmic width gives polynomial overhead despite an arbitrarily large union.

**Conditional consequence of the released arithmetic lower bound.** For polynomial-size lifts of the Hamiltonian-cycle *count* on Boolean inputs over a fixed field, width must be Ω((log m)^(4/3)). Otherwise the compiler would give a circuit below the released lower bound for the formally multilinear cycle polynomial. Here w≤m² for an m×m input; take logs to absorb the polynomial s(w+1) factor. This leaves both gaps open: there is no such width guarantee for arbitrary lifts, and fast decision does not give modular counts.

## Why one cut of a Boolean truth table cannot supply the unrestricted bound

For n-bit strings x,y, take the parity of their inner product. An unrestricted Boolean circuit computes this with n AND gates and n−1 binary XORs (or only a constant-factor more gates in an AND/OR/NOT basis). Nevertheless its sign matrix H(x,y)=(-1)^(x·y) has real rank 2^n: the row inner product for x,x′ is Σ_y (-1)^((x+x′)·y), which is 2^n if the rows agree and zero otherwise by pairing terms on one differing coordinate. Thus an O(n)-gate Boolean circuit can have maximum rank across a fixed input split. This is a sanity check against directly importing a flat cut-rank statistic, not an obstruction to multi-cut or composition-sensitive invariants, and not a flaw in [the arithmetic proof](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp).

## Map of the nearby questions

- [P vs. NP](https://www.claymath.org/millennium/p-vs-np/) is uniform polynomial-time decision versus efficiently verifiable witnesses. For SAT, decision gives a witness by pinning variables one by one. Showing SAT lacks even nonuniform polynomial-size Boolean circuits would suffice for P≠NP; that is a stronger target, not a necessary intermediate milestone.
- [#P and counting](https://epubs.siam.org/doi/abs/10.1137/0208032) asks for the exact number of witnesses. A fast exact count gives a fast existence test; the reverse is not known in general. This is distinct from a modular count, and both are distinct from formal polynomial size.
- VP versus VNP compares arithmetic circuits with polynomial families formed from large sums of efficiently computable terms. The border version additionally rules out the formal approximations defined in the release. A broader lower bound within that arithmetic model still does not cross to Boolean decision without a transfer.
- [ETH](https://courses.cs.washington.edu/courses/cse599i/24sp/papers/ImpagliazzoPaturi_2001_jcss.pdf) asks for an exponential-time floor for 3-SAT in the variable count. A valid subexponential algorithm refutes that floor but can remain superpolynomial, so it does not give P=NP. Conversely a polynomial-time SAT algorithm would refute the floor as well.

## Exact finite replay

The following JavaScript expands only tiny Boolean multilinear polynomials over prime fields and checks that every product it forms is multilinear, then compares every Boolean input with the original DAG. The random generator is seeded. This is a bounded cross-check, not a proof or general-purpose implementation.
```javascript
const mod=(x,p)=>(x%p+p)%p;
function compile(G,p,n){
 const V=G.map(([op,x,y],i)=>op==='x'?1<<x:op==='c'?0:(0)); const O=G.map(()=>0),A=G.map(()=>0);
 for(let i=0;i<G.length;i++){const [op,x,y]=G[i];if(op==='+'||op==='*'){V[i]=V[x]|V[y];if(op==='*')O[i]=V[x]&V[y]}}
 for(let i=G.length-1;i>=0;i--){const [op,x,y]=G[i];if(op==='+'||op==='*'){A[x]|=(A[i]|O[i])&V[x];A[y]|=(A[i]|O[i])&V[y]}}
 const pc=(a)=>a.toString(2).replaceAll('0','').length;const memo=new Map(),zero=new Map(),con=(x)=>new Map(x===0?[]:[[0,x]]);
 const plus=(a,b)=>{let c=new Map(a);for(const [i,x] of b)c.set(i,mod((c.get(i)??0)+x,p));return c};
 const times=(a,b)=>{const c=new Map();for(const [i,x] of a)for(const [j,y] of b){if(i&j)throw Error('non-multilinear product');c.set(i|j,mod((c.get(i|j)??0)+x*y,p))}return c};
 function run(i,R,a){R&=V[i];a&=R;if(R&~A[i])throw Error('bad context');let k=[i,R,a].join(',');if(memo.has(k))return memo.get(k);
 let [op,x,y]=G[i],P;if(op==='c')P=con(mod(x,p));else if(op==='x')P=R&(1<<x)?con(Number(!!(a&(1<<x)))):new Map([[1<<x,1]]);
 else if(op==='+')P=plus(run(x,R,a),run(y,R,a));else{let o=O[i]&~R;P=zero;for(let b=o;;b=(b-1)&o){let d=con(1);for(let j=0;j<n;j++)if((1<<j)&o)d=times(d,(1<<j)&b?new Map([[1<<j,1]]):new Map([[0,1],[1<<j,p-1]]));P=plus(P,times(d,times(run(x,R|o,a|b),run(y,R|o,a|b))));if(!b)break;}}
 memo.set(k,P);return P;}
 const P=run(G.length-1,0,0);for(let a=0;a<1<<n;a++){let v=[];for(let [op,x,y] of G)v.push(op==='x'?Number(!!(a&(1<<x))):op==='c'?mod(x,p):mod(op==='+'?v[x]+v[y]:v[x]*v[y],p));let q=0;for(const [u,c] of P)if((u&a)===u)q+=c;if(mod(q,p)!==v.at(-1))throw Error('false');}
 return Math.max(...A.map((a,i)=>pc(a|O[i])));
}
let seed=19n, rand=n=>Number((seed=(1664525n*seed+1013904223n)%4294967296n)>>12n)%n;let checks=0;
for(let k=0;k<90;k++){const G=Array.from({length:5},(_,i)=>['x',i]);G.push(['c',k-30]);for(let j=6;j<18;j++)G.push([rand(2)?'+':'*',rand(j),rand(j)]);for(let p of [2,3,5]){compile(G,p,5); checks+=32;}}
const d=[];let out;for(let i=0;i<5;i++){let j=d.length;d.push(['x',3*i],['x',3*i+1],['x',3*i+2],['+',j,j+1],['+',j,j+2],['*',j+3,j+4]);if(i===0)out=j+5;else{d.push(['+',out,j+5]);out=d.length-1;}}console.log({randomCircuits:90,fields:3,randomCubeChecks:checks,disjointWidth:compile(d,3,15),disjointChecks:32768,globalOverlap:5});
```

Observed: 8,640 cube checks across 90 DAGs and three fields; 32,768 more on the five-gadget fixture over F₃, with global overlap 5 and local width 1. The unrestricted Boolean transfer remains open.
