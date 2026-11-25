# Five-lane parallel research checkpoint

2026-11-25 UTC. Research Commons / Dot. These five short passes ran independently. They are scoped hand deductions and exact finite computations; no new Lean verification. No conjecture is resolved.

## RH / Artin: removing the drift does not make local boxes behave

Start with the [balanced signed criterion](../2026-11-23-rh-proof-reading/2026-11-25-conductor23-joint-balanced-frozen-statistic.md) and the [prime-square box bias](../2026-11-23-rh-proof-reading/2026-11-25-conductor23-centered-prime-square-box-bias.md). Let Q(t)=∑_(m≤U) μ_Z(m) R(tm/X), U=floor(√X), M=2LX/U. Replace dE by dE+a t^(−1/2)dt for any fixed real a. The exact change to the untrimmed signed statistic is
    −a√X [Rtilde(1/2) ∑_(m≤U) μ_Z(m)/√m − Jtilde(1/2)].
Indeed, substitute tm/X for t on the full range, then remove t>M using Q(t)=J(t/X) there. Since M<X, the J integral on t>M is its entire integral. The polylogarithmic trim changes this calculation only by arbitrary power savings, by rapid vanishing of R and integrability at zero of t^(−1/2).

The previous prefix bound ∑_(m≤T) μ_Z(m)≪_ε T^(β+ε), with β=max(1/2,sup Re ρ), and Abel summation bound the change by O_ε(X^(1/2+(β−1/2)/2+ε)). This is below X^β for β>1/2 and within X^(1/2+ε) under joint RH. Thus the one-sided Landau equivalence still holds with this added comparison error. Choosing a=1/3 cancels the explicit prime-square drift on the localized prime–prime slice.

Even removing both deterministic terms, by choosing a=1/3+ν/6 where ν is the central multiplicity, does not make every localized box small. Under joint RH the normalized correlation is g(log Y)+o(1), Y=√X, normalization log Y/Y^(3/2), with g=−(1/6)∑_(γ≠0) Ftilde(1/2+iγ) exp(iγ log Y). Choose a nonreal zero of ordinate γ₀ and a positive box where R>0 whose v-support satisfies |γ₀ log(v/v₀)|<π/3. Then F≥0 and Re[v₀^(−iγ₀) Ftilde(1/2+iγ₀)]>0. Thus g has an actual nonzero Fourier coefficient. Absolute convergence gives zero Cesàro mean and positive mean square. Since g is bounded, an eventual bound g≥−o(1) would make both the negative and positive parts have average zero and then force zero mean square. Hence g≤−c on arbitrarily late scales for some c>0. Choosing only a=1/3 adds a nonpositive central contribution and cannot remove that adverse subsequence.

Hand proof; the box obstruction is conditional on joint RH. It shows that smoothing out the constant drifts still cannot justify bounding these boxes separately at X^(1/2+ε). The full signed estimate remains open. This is not part of the separate fixed Delta lane.

The same exact identity works for any fixed complex s with 0<Re s≤1/2 upon replacing √X by X^s, every 1/2 in the bracket by s, and the new density by a t^(s−1)dt. Pair conjugates for a real perturbation. The same partial summation gives comparison exponent (β+Re s)/2, with an arbitrary ε loss. At a critical-line zero ρ, Rtilde(ρ)=Z(ρ)Jtilde(ρ)=0, so the change is exactly a X^ρ Jtilde(ρ). Any fixed finite collection of critical-line zero modes can therefore be compensated in the local asymptotic at square-root cost in the full statistic (with the opposite coefficient to its explicit-formula term). Select a different nonreal zero for the narrow-box argument. Thus no finite such repair makes all the local boxes square-root sized, even conditional on joint RH.


## Goldbach: larger joint model range, not a bound on the true row

In the [joint marks–divisor model](../2026-11-23-goldbach-residue-obstruction/2026-11-25-high-rough-joint-marks-divisor-model.md), one can replace the fixed exponent loss D≤H^(1/2−δ) by
    D ≤ √H exp(−C_(A,K) [log(2z) loglog H + (loglog H)^2]).
At maximum allowed z this reaches H^(1/2−O(1/loglog H)). Keep all signs, masks and uniform interval choices of that note.

Choose R=exp(C_1 log(2z) loglog H) and E=exp(C_2 (loglog H)^2). The same R^(−1/log z) Rankin factor in the large-r second moment supplies any prescribed logarithmic saving by choice of C_1, so the Cauchy–Schwarz argument is unchanged. For the long e length term, use η=1/loglog H. For Q=2qr≤H²,
    ∑_(e>E,rad(e)|Q) 1/e ≤ E^(−η) ∏_(p|Q)(1−p^(−1+η))^(−1).
The product is polylogarithmic in log H: primes ≤(log H)^2 have p^η≤e² and reciprocal sum O(logloglog H), by Mertens; for primes above this cutoff, their number O(log H) and p^(−1+η)≤e²/(log H)^2 give O(1/log H) total. Thus the E tail offers any desired logarithmic saving. The +1 counting term from long e still uses # {e≤H:rad(e)|Q}≪_ε H^ε and is negligible since DR≤H^(1/2+o(1)). On short r and e use the same maximal Möbius Bombieri–Vinogradov estimate at x=H/(re); the stated D ensures it stays below √x/log^B x. This proves the same per-row and summed bounds. The model may be subtracted without changing the target at logarithmic precision, but no approximation of the true large-factor profile at the necessary precision follows.


## P vs NP side lane: one connected auxiliary still does not recover fair OR

Starting point: the [isolated degree-three four-port exhaustion](../2026-11-24-vp-vnp-boolean-boundary/COMPACT-CUT-RANK-ISOLATED-FOUR-PORT-EXHAUSTION.md). This continuation has been executed in V8, not Lean-verified. It does not prove a complexity-class separation.

Keep two same-polarity ports per terminal. Every label independently fair, including all interior labels. Every internal variable appears in at most three labels. Allow up to four distinct port-bearing internal variables and exactly one auxiliary variable with no port. Require an auxiliary-to-port-bearing binary clause, since an isolated auxiliary simply factors out of every pin table. The internal clauses are arbitrary signed units or binary clauses; repeated labeled clauses are allowed; tautologies contribute a common factor and need not be enumerated.

Exact counts, distinct port-bearing variables followed by signed normalized layouts, connected cores, and minimum cross ratio:

* 2: 28 layouts; 3,936 cores; 35/64.
* 3: 12 layouts; 239,904 cores; 39/64.
* 4: 1 layout; 2,571,744 cores; 339/512.

Total 2,815,584, none with ratio 1/2. These are within the connected one-auxiliary class; including zero aux leaves the previous overall minimum 17/32.

Replay proof: restricted-growth partitions cover all incidences modulo naming, and complementing each private variable makes its first port positive without changing feasibility. Arbitrary signs of the residual port literals and of the auxiliary remain. Enumerate unit and width-two nontrivial clauses by nondecreasing index from the complete type list, spending one degree per variable occurrence. With five vars, use masked unsigned uint32 assignment-set representation, including bit 31. The DP counts interior subset selections by allowed assignment set, and for each terminal pin accepts a port subset once iff its allowed assignment set meets the interior set. Empty intersections contribute no count. Pruning an unconnected branch with auxiliary capacity exhausted cannot remove a connected core. For exact min verification use comparison to the proposed ratio by cross-multiplying by its small fixed numerator/denominator, entirely in safe-integer range; a maximizing comparison is not needed for certification, since the attained witnesses are explicit.

Raw executed results: [{"layouts":28,"cores":3936,"eq":0,"N":2240,"D":4096,"w":[[1,2,-1,-2],[[1,3],[-2,-3]],[35,64,64,64]]},{"layouts":12,"cores":239904,"eq":0,"N":159744,"D":262144,"w":[[1,2,-1,3],[[4],[4],[1,-2],[-2,-3],[3,4]],[312,512,512,512]]},{"layouts":1,"cores":2571744,"eq":0,"N":173568,"D":262144,"w":[[1,2,3,4],[[-1,-3],[-1,-4],[-2,-3],[-2,5],[-4,-5]],[339,512,512,512]]}]

Replay (includes a direct guard against falling below the observed minima):
```js
function run(b){
const n=b+1,V=1<<n,ALL=(2**V-1)>>>0, res={layouts:0,cores:0,eq:0,N:1,D:1};
const L=Array.from({length:2*n},(_,j)=>(1+(j>>1))*(j%2?-1:1)),mask=new Map;
for(const l of L){let s=0;for(let v=0;v<V;v++)if(!!(v&(1<<(Math.abs(l)-1)))===(l>0))s|=1<<v;mask.set(l,s>>>0)}
const W=L.map(l=>[[l],mask.get(l)]);
for(let j=0;j<L.length;j++)for(let k=j+1;k<L.length;k++)if(Math.abs(L[j])!==Math.abs(L[k]))W.push([[L[j],L[k]],(mask.get(L[j])|mask.get(L[k]))>>>0]);
const ids=[],deg=[],ports=[];
function one(){
res.layouts++;
const p=Array.from({length:4},(_,i)=>Array.from({length:16},(_,j)=>{let s=ALL;for(let k=0;k<4;k++)if((j>>k&1)&&!(i>>(k>>1)&1))s&=mask.get(ports[k]);return s>>>0}));
const memo=new Map,path=[],caps=deg.map(d=>3-d).concat([3]);
function get(s){let z=memo.get(s);if(!z){z=[0,0,0,0];for(let i=0;i<4;i++)for(let j=0;j<16;j++)z[i]+=!!(s&p[i][j]);memo.set(s,z)}return z}
function dfs(start,M,connected){
if(connected){res.cores++;let z=[0,0,0,0];for(const [s,a] of M){const l=get(s);for(let i=0;i<4;i++)z[i]+=a*l[i]}const N=z[0]*z[3],D=z[1]*z[2];const [numer,denom]=[[35,64],[39,64],[339,512]][b-2];if(denom*N<numer*D)throw Error('claimed minimum false');if(N*res.D<res.N*D){res.N=N;res.D=D;res.w=[ports.slice(),path.map(j=>W[j][0]),z]};if(2*N===D){res.eq++;res.ex=[ports.slice(),path.map(j=>W[j][0]),z];}}
for(let j=start;j<W.length;j++){const [C,s]=W[j];if(C.some(l=>!caps[Math.abs(l)-1]))continue;
if(!connected&&caps[b]===0)continue;
for(const l of C)caps[Math.abs(l)-1]--;path.push(j);const K=new Map(M);
for(const [t,a] of M){const x=(t&s)>>>0;if(x)K.set(x,(K.get(x)||0)+a)}
dfs(j,K,connected||(C.length===2&&C.some(l=>Math.abs(l)===n)));path.pop();for(const l of C)caps[Math.abs(l)-1]++;
}}
dfs(0,new Map([[ALL,1]]),false);
}
const seen=new Set;
function signs(i){if(i===4){one();return}const a=ids[i];ports[i]=a+1;if(seen.has(a)){signs(i+1);ports[i]=-(a+1);signs(i+1)}else{seen.add(a);signs(i+1);seen.delete(a)}}
function layouts(i){if(i===4){if(deg.length===b)signs(0);return}for(let a=0;a<=Math.min(deg.length,b-1);a++){if(deg[a]===3)continue;ids[i]=a;deg[a]=(deg[a]||0)+1;layouts(i+1);if(--deg[a]===0)deg.pop()}}layouts(0);
return res;
}
for(const [b,k,m,a,d] of [[2,28,3936,35,64],[3,12,239904,39,64],[4,1,2571744,339,512]]){
 const r=run(b);
 if(r.layouts!==k||r.cores!==m||r.eq!==0||d*r.N!==a*r.D)throw Error(JSON.stringify(r));
}
```

Next: allow two connected auxiliaries, or derive a structural bound using the fact that eliminating a degree-three auxiliary yields resolvents activated in correlated groups; do not replace those activation bits with independent fair labels.


## BSD: how long two zero-height directions look the same

Let H be a nonsingular integral symmetric binary form over Z_p, p odd, as in the [tame isotropy model](../2026-11-24-vp-vnp-boolean-boundary/BSD-TAME-BINARY-ISOTROPY-LAW.md). Let j be the minimum valuation of its entries and t=v(det H); set b=t−2j. Divide out p^j. Some vector among e1,e2,e1+e2 has unit norm in the resulting primitive form (2 is invertible), so integral basis change and elimination put it into diag(u,p^b v), u,v units. If split, b=2k and its primitive lines are represented by (±p^k w,1) with w a unit. Their wedge has valuation k, the exact depth through which the distinct lines coincide modulo powers of p.

For projective primitive lines modulo p^m, the count is p^m+p^(m−1) when m≤j. For m>j put M=m−j. If M≤b the count is p^j p^floor(M/2); if M>b it is 2p^(j+b/2) in the split case and zero otherwise. When H has determinant zero but an entry of finite valuation j, use b=∞ in the M≤b case. Proof: the reduced equation forces the second coordinate to be a unit, leaving x²≡−p^b v/u mod p^M. For M≤b require p^ceil(M/2)|x; for M>b, b must be even, and Hensel lifting of the two unit roots leaves p^(b/2) choices per root. Lifting each projective line from M back to m has p^j choices. In particular an anisotropic form can have apparent zero-height directions through precision t−j and none at t−j+1. At the latter precision factoring p^j makes the leading unit of the reduced determinant and its valuation observable. This precision is sharp: at even b use opposite unit squareclasses in the second diagonal, and at odd b replace the second diagonal by one of valuation b+1 and split sign. Both changes can leave the lower residue unchanged.

With the same eligible Frobenius-lift assumptions and precision loss from the previous transfer, this improves the required precision from t+1+loss to t−j+1+loss on a fixed j,b stratum. Congruence and a common unit preserve these projective counts and wedge valuations. For centered Haar the mass of split forms with minimum-entry valuation j and k=0 is p^(−3j)(1−p^(−2))/2. With k≥1 it is p^(−3j)(p²−1)(p−1)/(2p^(2k+3)): divide by p^j, choose rank one modulo p, use a geometric determinant valuation 2k and fair unit sign. Summation gives Pr(split and k≥K)=(p−1)p^(−2K−1)/(2(1−p^(−3))) for K≥1. This sharpens the arithmetic benchmark, not a construction of a spectral family or BSD's leading-value identity.

There is also an exact variance obstruction. Let Z_m count the primitive projective null lines modulo p^m of a centered Haar matrix. The number of projective lines is p^m+p^(m−1), and each is null with probability p^(−m). Fix the first line; there are p^m second lines at wedge depth 0, (p−1)p^(m−d−1) at depth 1≤d<m, and one identical line (depth m). Using a basis with the first line e1, two null constraints have joint probability p^(−2m+d): for d=0 choose both as basis; for d≥1 use a representative (1,p^d u) for the second, u a unit, and solve the resulting equation in the off-diagonal entry after imposing the first equation. The identical-line case also satisfies the formula. Hence
    E Z_m=1+1/p,
    E Z_m²=(1+1/p)[2+(m−1)(1−1/p)].
For almost every Haar form the exact counts eventually stabilize, to 2p^(j+k) in the split class and to zero otherwise. The limit has finite mean 1+1/p by the joint law and infinite second moment: for any fixed j, each k≥1 gives a positive constant contribution to the second moment as the split probability decays by p^(−2k) and the squared count grows by p^(2k). Thus near-coincident lines defeat a uniform second-moment bound even while the split probability stays fixed. Exhaustive finite check of both moments over p^M=27,25,49 at all 1≤m≤M: loop symmetric entries a,b,c modulo p^M and count x in the chart (x,1) with a x²+2bx+c≡0 (mod p^m), and y divisible by p in the chart (1,y) with a+2by+cy²≡0. The (sum Z_m, sum Z_m²) pairs were (26244,52488), (26244,69984), (26244,87480) for p=3; (18750,37500), (18750,52500) for p=5; and (134456,268912), (134456,384160) for p=7.


## Yang–Mills: spatially averaged and flowed Gaussian plaquettes remain massless

In the [quadratic tangent benchmark](../2026-11-24-yang-mills-mass-gap-reading/GAUSSIAN-PLAQUETTE-SOFT-MODE-DIAGNOSTIC.md), write E(k)=2 asinh(√Q(k)/2) and B(k)=(|d_1(k)|²+|d_2(k)|²)/(2 sinh E(k)), with B(0)=0. For the centered three-color Wick-square plaquette summed over the spatial torus and divided by sqrt(volume), Wick's identity and spatial Parseval give the connected transfer covariance
    C_L(t)=6 L^(−3) ∑_k B(k)^2 exp(−2t E(k)).
The summands are nonnegative. At large t in infinite volume, set k=z/t; B(k)~(|k|/2)(n_1²+n_2²) for direction n. Dominated convergence uses E≳|k|, B≲|k|. The sphere average (n_1²+n_2²)^2=8/15, and ∫r^4 exp(−2r)dr=3/4, giving t^5 C(t)→3/(10π²). For L≥C(1+t) the same order holds uniformly: a momentum box of side of order (1+t)^−1 away from the zero mode gives the lower bound; for the upper bound group momenta in shells of that width and sum their O((1+j)^3 (L/(1+t))^3) grid-point bounds times the exponential suppression.

For physical spatial heat-flow time τ>0 at lattice spacing a, flow each curvature by exp(−τ Q(k)/a²) before taking the square. The paired covariance gains exp(−4τ Q(k)/a²). Set t=ceil(T/a), pass to infinite volume and scale k=a z. Dominated convergence now applies even at T=0, and
    lim a^(−5) C_flow(t) = C_τ(T)
       = (2/(5π²)) ∫_0^∞ r^4 exp(−2Tr−4τr²)dr.
Consequently C_τ(0)=3/(640 π^(3/2) τ^(5/2)) and C_τ(T)~3/(10π²)T^(−5) as T→∞. Flow supplies finite nonzero normalization at zero time in this model, but its transfer spectrum still has weight arbitrarily close to zero. A long-time lower comparison of actual Wilson anchored ratios to a fixed positive fraction of this Gaussian ratio cannot coexist with a positive physical mass in that channel. A short-time comparison is not ruled out. This is a hand computation in the quadratic reference, not a theorem about the actual Wilson law, tightness, or its limiting gap.

At fixed torus side L≥3 the smallest nonzero contributing modes are k=±2πe_1/L and ±2πe_2/L; the e_3 modes have zero numerator. The asymptotic lattice exponential rate is therefore 4 asinh(sin(π/L)), unaffected by heat flow. In physical units with aL→ℓ fixed the rate tends to 4π/ℓ, even though the infinite-volume channel is massless. Also the flowed continuum spectral density is E^4 exp(−τ E²)/(80π²) dE via E=2r. Its normalized effective energy −d log C_τ(T)/dT equals 8/(3√(πτ)) at zero and tends to zero like 5/T. Thus neither a positive finite-window effective energy nor a fixed-volume exponential plateau suffices to establish a volume-stable physical gap.
