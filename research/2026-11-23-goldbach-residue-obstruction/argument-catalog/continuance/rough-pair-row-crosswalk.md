# Goldbach: same-target crosswalk between two sieve counts

Finite diagnostic and support argument; no asymptotic estimate or Lean check. The rough-pair approach is due to the separate Codex coordinator's 18:13 UTC checkpoint; see [its public progress page](../../../../communications/2026-11-23-codex-number-theory-progress.md). The other count is [the signed modulus-3 moving-prefix row](character-centering.md). Their signs need not agree.

For even N coprime to 3, let z=floor(N^(1/3)), alpha=floor(sqrt(N)/2), and m=N−n. Call an endpoint rough if it is at least 2 and has no prime divisor at most z. Let R be the number of ordered endpoints for doubly rough pairs and P the number of those endpoints that are prime. Reflection gives G=2P−R+M, where G counts ordered prime–prime pairs in this set and M counts ordered composite–composite pairs. In particular, 2P−R>0 is sufficient but not necessary for a Goldbach pair.

The q=3 row retains the original cutoff 3 alpha<m<N and the summand c(m) Λ(n) μ(m) log(m/3), with c(m)=1/2 for m=0 mod 3 and −1/2 otherwise. On its overlap with doubly rough pairs and ordinary prime n, m can only be a prime or a squarefree product of two primes: three factors greater than z would exceed N, and μ removes squares. Thus each plotted overlap column counts only the actual prime–prime or prime–semiprime subset, not the full rough-pair margin. In contrast, that margin treats rough squares as composite and includes composite–composite pairs. On overlap for z≥3, c(m)=−1/2, so prime partners contribute positively and squarefree semiprime partners negatively, with no residue-sign cancellation within either class. Outside the overlap, composite m with smallest prime at most z may contribute at either sign. The ordinary prime n≤z boundary is O(z log² N) in absolute mass. Strict prime-power n contributes O(sqrt(N) log² N), because there are at most sqrt(N) bases, each with total Λ weight at most log N.

## Exact counts and numerical weights

Selected prior stress targets plus 17 dyadics, 2^4 through 2^20. The margin is an exact count. All five signed columns are divided by N and use binary64 logarithms and accumulation. “Rough balanced” means distinct factors u≤v≤2u of m; “rough uneven” means v>2u. Those columns and “rough prime” require both endpoints rough and n prime. “Small factor” requires n prime and m composite with smallest factor at most z, including n≤z if applicable. The total also retains outside-overlap prime m, rough composite m with small n, and strict prime power n. Exact factor 2 is a diagnostic split, not the growing-factor split in the coordinator's separate analytic bound.

| N | 2P−R | Rough prime | Rough balanced | Rough uneven | Small factor | Full q=3 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 8834 | 162 | 0.555245 | -0.104105 | -0.207328 | -0.308047 | -0.061283 |
| 9602 | 125 | 0.452860 | -0.065476 | -0.173671 | -0.382414 | -0.158936 |
| 9896 | 164 | 0.532333 | -0.069753 | -0.170334 | -0.403967 | -0.115279 |
| 20654 | 302 | 0.607275 | -0.083571 | -0.202728 | -0.366383 | -0.040096 |
| 23750 | 414 | 0.804580 | -0.093600 | -0.290866 | -0.312976 | 0.103742 |
| 16 | 4 | 0.115689 | 0.000000 | 0.000000 | -0.033367 | 0.111411 |
| 32 | 2 | 0.141437 | 0.000000 | 0.000000 | 0.119218 | 0.355871 |
| 64 | 8 | 0.327483 | -0.064629 | 0.000000 | 0.206647 | 0.548670 |
| 128 | 6 | 0.262863 | -0.048130 | 0.000000 | 0.113658 | 0.386589 |
| 256 | 14 | 0.375547 | -0.100470 | -0.068049 | 0.126953 | 0.353304 |
| 512 | 18 | 0.419030 | -0.014670 | -0.083584 | -0.115284 | 0.250552 |
| 1024 | 36 | 0.506427 | -0.072815 | -0.141713 | -0.155036 | 0.131426 |
| 2048 | 46 | 0.410375 | -0.063022 | -0.185594 | -0.187403 | -0.011034 |
| 4096 | 90 | 0.524012 | -0.086071 | -0.171065 | -0.332463 | -0.066382 |
| 8192 | 126 | 0.493783 | -0.063115 | -0.157603 | -0.373833 | -0.106865 |
| 16384 | 246 | 0.582620 | -0.078867 | -0.162153 | -0.304300 | 0.043844 |
| 32768 | 404 | 0.568103 | -0.071442 | -0.179993 | -0.332669 | -0.012449 |
| 65536 | 670 | 0.589024 | -0.064332 | -0.236771 | -0.291690 | -0.004486 |
| 131072 | 1128 | 0.584026 | -0.063494 | -0.230047 | -0.273594 | 0.015526 |
| 262144 | 1952 | 0.585870 | -0.063314 | -0.247509 | -0.270102 | 0.006701 |
| 524288 | 3506 | 0.598768 | -0.061493 | -0.246176 | -0.315715 | -0.023077 |
| 1048576 | 6210 | 0.604015 | -0.062016 | -0.267709 | -0.277434 | -0.003600 |

The margin is positive at every target; the q=3 row is negative at 11 of 22. At N=9602 and N=2^20, respectively, the small-factor contribution is −0.382414N and −0.277434N, larger in magnitude than the doubly rough uneven-semiprime contribution (−0.173671N and −0.267709N). Therefore the existing bound for nearly equal rough factors cannot by itself account for the losses in the moving-prefix row. A pointwise transfer would also need to bound or cancel the small-factor contribution with the other terms; the experiments neither prove its growth nor test the combined error across moduli. Next isolate its smallest-factor slices and keep positive and negative signs on the same target, rather than charging each negative slice an independent budget.

## Replay (JavaScript)

```js
function run(){
const targets=[8834,9602,9896,20654,23750,...Array.from({length:17},(_,i)=>2**(i+4))],max=Math.max(...targets),spf=new Int32Array(max+1),mu=new Int8Array(max+1),pow=new Int32Array(max+1);mu[1]=1; for(let n=2;n<=max;n++){if(!spf[n]){spf[n]=n;if(n*n<=max)for(let k=n*n;k<=max;k+=n)if(!spf[k])spf[k]=n;}const p=spf[n],k=n/p;mu[n]=k%p===0?0:-mu[k];pow[n]=k===1||pow[k]===p?p:0;}
const results=[];for(const N of targets){let z=0;while((z+1)**3<=N)z++;const a=Math.floor(Math.sqrt(N)/2);let P=0,R=0,G=0,M=0,sq=0,bal=0,unbal=0; const w=Array(7).fill(0);let direct=0;const low={};
for(let n=1;n<N;n++){const m=N-n;const u=spf[m],v=u?m/u:0;const rn=n>=2&&spf[n]>z,rm=m>=2&&u>z,np=spf[n]===n&&n>=2,mp=u===m&&m>=2;const both=rn&&rm, rs=rm&&!mp&&spf[v]===v;
if(both){R++;P+=np;G+=np&&mp;M+=!np&&!mp;if(!mp){if(!rs)throw Error("support"); if(u===v)sq++;else if(v<=2*u)bal++;else unbal++;}}
if(m<=3*a||!pow[n]||!mu[m])continue;
const val=(m%3===0?.5:-.5)*Math.log(pow[n])*mu[m]*Math.log(m/3);direct+=val;
let j=!np?6:mp?(both?0:4):both?(v<=2*u?1:2):rm?5:3;w[j]+=val;if(j===3)low[u]=(low[u]||0)+val/N;
}
if(G!==2*P-R+M||R-P!==sq+bal+unbal||Math.abs(w.reduce((x,y)=>x+y,0)-direct)>N*1e-11)throw Error("identity");
results.push({N,z,P,R,G,M,sq,bal,unbal,low,weighted:w.map(x=>+(x/N).toFixed(7)),total:+(direct/N).toFixed(7)});
}return results;}
console.log(JSON.stringify(run(), null, 2));
```
