# Exact compact rank at fixed matching deficit via dual flats

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof using the classical matching-deficiency SAT theorem, with exact finite replay. No Lean verification, unrestricted polynomial-time result, or P versus NP separation.

For a CNF with m labeled clauses let d=m−r(E), where E is the clause-label ground set and r is the maximum clause-variable matching size on a subset. Keep nonnegative integer weights w_i(0) for omission and w_i(1) for inclusion. The [compact clause-subset rank](MIXED-GATE-CUT-RANK.md) is the number of satisfiable selections at unit weights; the weighted version sums their product weights. Unlike the [deficit approximation](DETERMINISTIC-FPT-DEFICIT-APPROXIMATION.md), the algorithm here returns the exact count. It makes at most sum_(i=0)^(d−1) binom(m,i) calls to a satisfiability algorithm, each on maximum deficiency at most d, with polynomial work in the input and that number. Use the convention that when d=0 no calls are needed. In particular exact counting is polynomial for each fixed d, but this is an XP bound, not an exact fixed-parameter tractability claim.

## The kernel determined by omissions

The matchable subsets form the transversal matroid M with rank r. Let S be the selected labels, U=E minus S the omitted labels, and M* the dual matroid. Write cl* for its closure. Define

    K = E minus cl*(U).

Then S is satisfiable exactly when K is satisfiable. Here is a proof that preserves clause labels and the original literal signs.

For a clause set T, write V(T) for its adjacent variables. The deficiency form of Hall's theorem gives |S|−r(S)=max_(T subset S)(|T|−|V(T)|), with value zero also possible. In the restriction M|S remove its coloops, the elements in every basis. The resulting set is exactly K: the dual rank formula r*(U)=|U|+r(E minus U)−r(E) shows for e in S that e lies in cl*(U) if and only if r(S)−r(S minus {e})=1. This is precisely the coloop test. Deleting all coloops preserves nullity, since they belong to every basis and removing them reduces rank and cardinality by the same amount. Also every subset T of S with the same nullity as S contains K: deleting any e outside T must preserve nullity by monotonicity of nullity, so e must be a coloop. Thus K is the smallest nullity-attaining subset of S. Apply Hall inside K to get some T subset K with |T|−|V(T)| equal to the nullity of K. The nullity of T is at least |T|−|V(T)|, and at most that of K. Hence T contains K by the preceding characterization, so T=K. In particular K attains the maximum deficiency in S, including K=empty when appropriate.

For any J subset of S minus K, maximality implies |V(J) minus V(K)|≥|J| by applying the deficiency bound to K union J. Hall now gives a matching of all labels outside K to distinct variables outside V(K). Keep any satisfying assignment to K and use each new variable to satisfy its distinct matched clause. There is no conflict with K, and every added clause has a literal made true. The converse is restriction. This is a matching-autarky argument; see [Fleischner–Kullmann–Szeider](https://ac.tuwien.ac.at/files/pub/fleischner-kullmann-szeider-2002.pdf) for the classical technique. We use it here to classify all omission sets rather than just to decide SAT once.

## Count all omission sets with a given flat

The dual rank is d. Every proper dual flat is the closure of a basis of size at most d−1 (a full-rank flat is E). Enumerate subsets of those sizes and deduplicate their proper closures, computing rank and closure from the dual rank formula and maximum matching. This enumeration can generate the subsets by increasing size without scanning all 2^m subsets.

For each proper flat D let
    W(D) = product_(i in D) (w_i(0)+w_i(1)) times product_(i outside D) w_i(1).
This is the total weight of omission sets U contained in D; equivalently their closure lies in D. In increasing order of flat size compute W_exact(D)=W(D)−sum_(C proper flat strictly inside D) W_exact(C). This requires no division and accommodates zero weights. The top flat E has empty kernel, always satisfiable, so its mass need not be computed separately. The answer is the total product of weight sums minus W_exact(D) for the proper flats with unsatisfiable kernel E minus D.

For each kernel use [Szeider's maximum-deficiency SAT algorithm](https://eccc.weizmann.ac.il/report/2003/002/revision/1/), which has 2^d times polynomial complexity on these inputs; maximum deficiency cannot increase under clause restriction. Standard formulations on clause-sets may first deduplicate identical clauses for the decision call only, which does not increase maximum deficiency or affect that call's answer. All ranks, flat weights and enumeration retain original label multiplicities. Total arithmetic has polynomial bit lengths (each mass is at most the total product) and the announced XP bound follows. At d=1 there is a single proper flat D, the dual loops. One SAT call on its complement suffices: with unit weights either the answer is 2^m, or it is 2^m−2^|D| if that kernel is unsatisfiable. The d=0 case is full matching and every selection is satisfiable.

The exponent comes from enumerating proper flats and inverting their inclusion order. This does not determine whether exact FPT in d is possible. The advance is from a relative estimate to an exact count for any fixed d, not a lower bound on general computation.

## Exact finite replay

Standalone JavaScript (replace text by console.log). The small-fixture enumeration uses bit masks, not the production subset generator or Szeider's SAT algorithm. It checks 480 formulas and 56,624 selections against independent exhaustive assignment search, including 85 formulas of deficit one. It checks both the satisfiability invariant for every selection and the resulting weighted count.

```javascript
function profile(F,n){
 const m=F.length,E=(1<<m)-1,N=1<<m;
 const pc=x=>{let k=0;while(x){x&=x-1;k++}return k};
 const sat=S=>{for(let x=0;x<1<<n;x++)if(F.every((C,i)=>!(S>>i&1)||C.some(l=>Boolean(x>>(Math.abs(l)-1)&1)===(l>0))))return true;return false};
 const rank=S=>{
   const a=Array(n).fill(-1);
   function dfs(i,seen){for(const l of F[i]){
      const j=Math.abs(l)-1;if(seen[j])continue;seen[j]=1;
      if(a[j]<0||dfs(a[j],seen)){a[j]=i;return true;}
   }return false;}
   let k=0;for(let i=0;i<m;i++)if((S>>i&1)&&dfs(i,[]))k++;return k;
 };
 const re=rank(E),d=m-re;
 const dr=U=>pc(U)+rank(E^U)-re;
 const cl=U=>{let A=U,r=dr(U);for(let j=0;j<m;j++)if(!(U>>j&1)&&dr(U|(1<<j))===r)A|=1<<j;return A;};
 return {E,N,d,pc,sat,cl};
}
let s=343132;
const rnd=n=>((s=(Math.imul(s,1664525)+1013904223)>>>0)>>>9)%n;
let checked=0,selections=0,d1=0;
for(let i=0;i<480;i++){
 const n=1+rnd(6),m=1+rnd(9), F=Array.from({length:m},()=>Array.from({length:n},(_,j)=>rnd(5)===0?(rnd(2)?1:-1)*(1+j):0).filter(Boolean));
 const a=F.map(()=>[BigInt(rnd(4)),BigInt(rnd(4))]), {E,N,d,pc,sat,cl}=profile(F,n);
 if(d===1)d1++;
 const w=U=>a.reduce((p,x,j)=>p*x[U>>j&1],1n); // array order: include, omit
 const flats=[...new Set(Array.from({length:N},(_,U)=>U).filter(U=>pc(U)<d).map(cl))].sort((a,b)=>pc(a)-pc(b));
 const B=new Map();let ans=w(0)*0n, reference=0n,total=0n;
 for(let U=0;U<N;U++){
   const wt=w(U);total+=wt;
   if(sat(E^U)!==sat(E^cl(U)))throw Error('kernel '+i+' '+U);
   if(sat(E^U))reference+=wt;
   selections++;
 }
 ans=total;
 for(const D of flats){
   let b=a.reduce((p,x,j)=>p*((D>>j&1)?x[0]+x[1]:x[0]),1n);
   for(const [C,t] of B)if((C&D)===C)b-=t;
   B.set(D,b);if(!sat(E^D))ans-=b;
 }
 if(ans!==reference)throw Error('rank '+i);
 checked++;
}
text({checked,selections,d1});
```
