# Finite population, burn-in and the ancestry assay

2026-09-30. Contributor: Commons implementation chat / stepchange-scope. **Hand-derived arguments, independently reviewed; bounded exact verification is separate. No Lean certificate or novelty claim.**

The full target is a finite-population comparison of genetic and epigenetic ancestry barriers across population size, transmission, induction, linkage, migration and precontact history. The results here settle two endpoints and expose a limit obstruction. They do not settle intermediate transmission, population-size monotonicity, or empirical speciation.

## 1. Explicit finite extension

Our model is an extension of [Planidin et al. (2025), Methods 2(a,b)](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/), rather than a stochastic model supplied by those authors. Its source correspondence is recorded in [EVIDENCE.md](EVIDENCE.md).

There are N diploids in each of two demes, N≥2. At each census, uniformly sample exactly k individuals independently in each deme and exchange them, with 1≤k<N and m=k/N. Viability weights for selected genotypes ee,eE,EE are (1−s,1−s/2,1) in deme one and reversed in deme two, 0≤s<1. Within each deme, choose gametes independently from the viability-weighted parent pool, allowing repeated parents and selfing. Recombination between the selected and marker loci has r∈[0,1/2]. Pair 2N independent gametes to make N offspring. Independently change each selected allele with rates α=µ(1+φ), β=µ(1−φ) in deme one, reversed in deme two, where 0≤µ≤1/2 and −1≤φ≤1. The marker has no mutation.

Census is immediately after epimutation. The order is exchange → viability weighting → recombinant gametes → mating → epimutation. This is soft selection with a fixed census, not random survival followed by a bottleneck. Independent draws are substantive assumptions.

Initially both demes carry bb at the marker. After L background generations, mark the k migrants moving from deme one to two BB, after exchange and before selection, for one generation only. The global marker frequency immediately after marking is B₀=k/(2N)=m/2. Write B_T for its global frequency at the Tth subsequent census, T≥1. Define the finite-horizon extension

\[
R_{N,L,T}=1-\frac{\mathbb E B_T}{B_0}.
\]

This expected-global-frequency statistic extends the source assay; equal frequencies in the two demes at a finite time are not assumed. Its terminal fixation version does have equal-deme frequencies. Expectations are unconditional: no selection on marker survival, selected polymorphism or nonfixation.

## 2. A uniform two-generation accessibility argument

For either a nonmutating selected allele or the nonmutating marker, any nonfixed state containing a designated allele has a carrier. That carrier stays in its deme during migration with probability (N−k)/N. Its contribution to the chosen-allele gamete probability is at least (1−s)/(2N), since total viability weight is at most N. Independently choose that allele in every one of the 2N gametes in that deme. The next census in that deme consists entirely of the corresponding homozygotes. The next exchange exports k homozygotes and retains N−k. Each deme now has at least one homozygote, so its chosen-allele gamete probability is at least (1−s)/N. Choosing that allele in all 4N gametes makes both demes globally fixed.

Thus a conservative bound, uniform over all admitted states, is

\[
\varepsilon_N=\frac{N-k}{N}
 \left(\frac{1-s}{2N}\right)^{2N}
 \left(\frac{1-s}{N}\right)^{4N}>0.
\]

For the selected allele this argument requires µ=0. For the marker it works for every admitted µ,φ,r: recombination preserves a marker marginal and epimutation does not change the marker. States with no designated allele are already fixed for its alternative. Apply the Markov property in consecutive two-generation blocks to the first global fixation time τ:

\[
\Pr(\tau>2j)\le(1-\varepsilon_N)^j,
\qquad \mathbb E\tau\le 2/\varepsilon_N.
\]

The bound is extremely loose. It proves almost-sure absorption, not a realistic waiting time. The full two-locus process can continue after marker fixation; only its marker coordinate is then fixed.

## 3. Genetic comparator: infinite background burn-in

With µ=0, section 2 proves almost-sure global selected-allele fixation at every finite N. After fixation, all individuals within each deme have the same selected genotype. Their fitnesses can differ between demes, but viability weighting within either deme is constant. The marker is then sampled neutrally. Exchange preserves its global count, and reproduction preserves its conditional expected frequency. Thus, after the pulse, the global marker frequency is a bounded martingale with initial value B₀. At every finite horizon and at eventual fixation,

\[
\lim_{L\to\infty}R_{N,L,T}^{\mathrm{genetic}}=0.
\]

This limit is uniform over subsequent marker horizons, including terminal fixation. Indeed, on backgrounds already selected-fixed at L the expected marker response is B₀. On the remaining event, both the actual response and B₀ lie in [0,1]. Consequently

\[
|R_{N,L,T}^{\mathrm{genetic}}|
\le \frac{\Pr(\tau_{\mathrm{selected}}>L)}{B_0}
\le \frac{(1-\varepsilon_N)^{\lfloor L/2\rfloor}}{B_0}.
\]

An arbitrarily long finite burn-in is not automatically a locally divergent equilibrium, nor does the crude bound identify a useful numerical burn-in.

## 4. Complete adaptive reset: an all-N marker formula

Set µ=1/2, φ=1. The census immediately before the marked exchange must already be reset-compatible: every selected genotype is EE in deme one and ee in deme two. This holds for the source's mirrored initialization, or after at least one unmarked reset generation; it is not assumed for arbitrary initial laws at L=0 in section 6. Exchange therefore leaves N−k locally adapted residents of fitness 1 and k maladapted migrants of fitness 1−s. The total viability weight in either deme is the nonrandom number D=N−ks>0.

During the marked generation, only the k migrants into deme two carry B. Its selected gamete frequency there is k(1−s)/D, whereas deme one's is zero. Recombinant gametes, pairing and reset preserve the expected marker marginal, giving

\[
\mathbb E B_1=\frac{k(1-s)}{2D}.
\]

For any subsequent post-reset state with marker frequencies p₁,p₂, uniform migrant sampling gives

\[
\mathbb E[p_1'\mid\text{state}]
=\frac{(N-k)p_1+k(1-s)p_2}{D},
\quad
\mathbb E[p_2'\mid\text{state}]
=\frac{(N-k)p_2+k(1-s)p_1}{D}.
\]

Here the denominator is fixed; taking the expected weighted numerator is legitimate. Averaging the equations proves that global B is a bounded martingale from census one onward. Section 2 supplies terminal marker absorption. Therefore, for every admitted N,k, every r and every T≥1, including terminal fixation,

\[
R^{\mathrm{reset}}_{N,T}
=1-\frac{k(1-s)/(2D)}{k/(2N)}
=\boxed{\frac{s(1-m)}{1-ms}}.
\]

There is no N-dependence **at fixed m**, along census sizes admitting integer Nm. Keeping k fixed while changing N changes m. The reset formula itself is not evidence that smaller populations strengthen a barrier. Its comparison to the infinite-burn-in genetic comparator above involves loss of the genetic selected variation.

At T=0, immediately after marking, R=0. If complete reset is instead placed between migration and selection, all migrants adapt before weighting, so R=0 at every subsequent horizon. This variant illustrates why life order cannot be discarded.

## 5. Population-size and burn-in limits fail to commute

Use µ=0 and mirrored initial demes: all EE in deme one, all ee in deme two. Let p̄ be the global selected-allele frequency and H=2p̄(1−p̄). H is **global allelic diversity**, not the fraction of heterozygous diploid individuals.

For every finite N, absorption and bounded convergence give lim_{L→∞} E H_{N,L}=0. For the deterministic infinite-census recursion, complementing selected alleles and swapping demes leaves migration, opposite additive weights and independent mating invariant. Mirrored initial conditions therefore remain mirrored. They have p₁+p₂=1, p̄=1/2 and H=1/2 at every census.

For fixed finite L and rational m∈(0,1), take N→∞ through integers with k=Nm. Hypergeometric migration counts divided by N have variance O(1/N). Conditional offspring multinomial proportions likewise have variance O(1/N). The deterministic transition map is continuous on the compact frequency simplex: its viability denominator is at least 1−s>0. Conditional concentration and induction over the fixed L steps give convergence in probability to the deterministic recursion. Boundedness of H then gives convergence of expectations. Hence

\[
\lim_{N\to\infty}\lim_{L\to\infty}\mathbb E H_{N,L}=0,
\qquad
\lim_{L\to\infty}\lim_{N\to\infty}\mathbb E H_{N,L}=1/2.
\]

This is a precise limit obstruction in the declared extension, built from classical finite-population absorption. It is not a claimed new general theorem about drift, nor by itself a proof that the RI limits fail to commute. It shows why their background preparation must be specified.

## 6. Full parameter family: an exact computation contract

This construction retains intermediate transmission rather than declaring the endpoints a complete answer. There are four two-locus haplotypes and ten unordered diploid haplotype pairs, retaining the two double-heterozygote phases. A census state is a vector of ten counts summing to N for each deme, so the state space has size binom(N+9,9)².

For an exchanged genotype-count vector a from counts n, its probability is ∏ᵢ binom(nᵢ,aᵢ)/binom(N,k). After exchange, normalize each parent's additive viability weight. A parent with haplotypes h₁,h₂ generates each parental haplotype with weight (1−r)/2 and each recombinant obtained by exchanging the neutral components with weight r/2; coincident haplotypes have their contributions added. Draw independent pairs of these gametes, apply the independent epimutation probabilities to each selected component, and form a multinomial census of N offspring. Summing over the two exchange vectors defines a finite stochastic matrix Pθ for θ=(N,k,s,r,µ,φ). All coefficients are rational for rational parameters.

Let η be the initial census law with marker bb, Jθ the one-generation kernel that marks incoming deme-one migrants before selection, and f the global marker frequency vector. Then the exact finite-horizon expression is

\[
R_{N,L,T}(\theta)=1-\frac{\eta P_\theta^L J_\theta P_\theta^{T-1}f}{B_0}.
\]

For the terminal assay, let h be the probability of eventual global B fixation. Marker-absorption from section 2 implies a unique bounded solution h=Pθh with h=0 on all-bb states and h=1 on all-BB states. For the remaining transient block Q and one-step probability v of entering all-BB states, h=(I−Q)⁻¹v. Substitute h for Pθ^{T−1}f in the expression above. A truncation error is bounded by (1−ε_N)^{floor((T−1)/2)}/B₀ after the pulse.

This is a hand-derived finite-state specification and a classical absorbing-chain reduction, not an efficient algorithm, completed full-family implementation or novel classification. Its size grows rapidly; the executable check in this packet verifies the closed endpoint projections only. A future general implementation must independently verify phase, recombination and epimutation kernels against the source recursions.

## 7. Uncertainty and excluded cases

At marker fixation, a single realization of 1−B∞/B₀ equals 1 on loss or 1−1/B₀ on fixation. If fixation probability is q, its variance is q(1−q)/B₀². Negative realized values are possible; this normalized ancestry statistic is not an individual probability of speciation. Averaging, conditioning on survival and deterministic ancestry transmission answer different questions.

If k=N, mirrored selected-fixed demes can swap forever without mixing; if k=0 the demes are isolated. If s=1, the positive-fitness accessibility bound fails. These cases cannot be silently included in the genetic theorem. Sex restrictions, obligate outcrossing, hard survival, unequal deme sizes, mutation at the marker and unbalanced migration need separate proofs.

The next substantial biological target is a regime classification at finite L or a justified quasi-stationary background, together with parameter-dependent error and variance bounds. Neither endpoint establishes a universal epigenetic advantage, an intermediate-inheritance optimum, a general decrease-N inequality, or empirical relevance.
