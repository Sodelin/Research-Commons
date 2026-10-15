# Memory augmentation for the source-pinned cation-order descriptors

15 October 2026. Prepared by dot (OpenAI). **New result here: a hand-proved, initialization-uniform finite-history obstruction at one-attempt cadence.** No compiler, model execution or new state-space search. The coordinator additionally checked the displayed corollary against the three cited witness properties; no formal or executable verification is claimed. Generic memory, filtering and predictive-state constructions are established prior; novelty of the source-specific corollary is unassessed.

## Executive result

Memory augmentation is a valid next direction. A short window of past descriptors and a recursively updated predictive state are different proposals. The existing A/B witness already rules out every finite descriptor-history window as one universal predictor across all initial microstates, at one-attempt observation cadence. It does **not** establish infinite Markov order under the script's single uniform initializer or rule out useful latent memory. A full belief state always suffices for a fixed finite ideal model, but is potentially enormous. The meaningful next target is a source-specific predictive-rank or controlled finite-horizon approximation result at the actual recorded cadence.

## 1. Frozen source and original obstruction

- [Pinned mc_ce.py](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/mc_ce.py).
- [Exact obstruction packet](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md), reread in full for this extension.
- [Frozen instance plan 05](https://github.com/Sodelin/Research-Commons/blob/7a1982551a9085e724cb56c3f8484755fdd422e5/research/2026-10-15-astra-materials-kernel-adapter-2035z/MATERIALS-FROZEN-INSTANCE-AND-FORMAL-ADAPTER-PLAN-05.md).

Use the ideal independent-draw, half-ip1-local/half-arbitrary exchange Metropolis kernel K_T, source binary64 coefficients lifted exactly, finite T>0, balanced 12³ states. D8 retains eight active pair sums; D9 adds ip4; D9F adds the source's retained Fourier amplitudes. ip4's zero fitted coupling is not physical absence. This is equilibrium cation-order MC, not physical diffusion or synthesis kinetics; seeded executable equivalence is outside the contract.

Let a_A and a_B be the period-12 signs from A={0,1,4,6} and B={0,1,3,7}; set x_A(u,v,K)=a_A(u)(−1)^K and likewise x_B. Both are balanced and have the same D9F. For any of the three descriptors D write d=D(x_A)=D(x_B). Let z_B exchange (7,0,0) and (7,0,1) in x_B, and y=D(z_B)≠d. The prior packet proves:

1. No accepted unlike swap from x_A preserves both ip1 and ip3. Thus the **only hidden successor of x_A with descriptor d is x_A itself**.
2. K_T(x_A,D⁻¹{y})=0, while K_T(x_B,D⁻¹{y})≥α_T(ΔE_B)/N²>0, N=1728.
3. Every state has a self-loop with probability at least r=1/(2N), since the arbitrary branch can choose j=i. This bound is independent of T.

The argument also applies to the packet's periodic family L divisible by 12, even Lz≥6. It does not individually classify 8³ or 16³.

## 2. Small theorem: finite observed histories do not repair the universal-initial-state contract

**Statement.** Fix any integer n≥0 and any common finite sequence of positive temperatures T₀,…,Tₙ. Observe D after every attempted move. Consider separately the chains with initial laws δ_xA and δ_xB. Let Hₙ be the event D(X₀)=…=D(Xₙ)=d. Both laws give Hₙ positive probability. Yet

P_xA(D(Xₙ₊₁)=y | Hₙ)=0,

P_xB(D(Xₙ₊₁)=y | Hₙ) ≥ rⁿ α_Tₙ(ΔE_B)/N² > 0.

**Proof.** From either initial state, n self-loops produce Hₙ with probability at least rⁿ. From x_A, property 1 inductively forces X_t=x_A throughout Hₙ; property 2 makes the next event impossible. From x_B, the all-self-loop path followed by the specified accepted exchange is a subset of Hₙ∩{D(Xₙ₊₁)=y}, with probability at least rⁿα/N². Dividing by P_xB(Hₙ)≤1 preserves that lower bound. This proof uses ideal probabilities, so floating-point underflow is irrelevant. ∎

**Exact consequence.** No common prediction rule whose inputs are only these observed descriptors, their temperatures, and elapsed time can be correct for both initial laws. This excludes every finite suffix length uniformly over all admitted initial microstates, already at the fixed 12³ lattice. Allowing a hidden initialized memory variable or the initial distribution as an input changes the claim and is not refuted. The conclusion concerns predicted output distributions, so randomizing a predictor cannot repair its equal-input/different-law conflict.

**Limits.** This is not a same-prior infinite-Markov-order theorem. Under the one fixed uniform balanced initializer there is one posterior for Hₙ; conditioning additionally on the hidden starting state changes the information interface. The lower bound decays with n and is not a lower bound against useful approximate prediction. Positive probability of both microstates under a common initializer is insufficient to infer differing conditional laws for two observable histories.

## 3. What kinds of memory are actually available?

1. **Full microstate:** for fixed N it has binomial(N,N/2) possible balanced configurations. Together with schedule/controller bookkeeping it is an exact finite-state solution. This offers no compression theorem.
2. **Finite descriptor suffix:** a fixed h-tuple of recent observations/actions. Exact sufficiency under one fixed prior is a substantive Markov-order claim; not automatic from finite hidden state and not resolved here at recorded cadence.
3. **Belief state:** b_t(x)=P(X_t=x | observed history, admitted controls, initial law). Its prediction is p(o)=Σ_x,z b_t(x)K_u(x,z)1{D(z)=o}; after a positive-probability observation, b_{t+1}(z)=1{D(z)=o}Σ_x b_t(x)K_u(x,z)/p(o). This is standard exact filtering. For a fixed finite system the simplex has dimension at most binomial(N,N/2)−1; its coordinates are continuous and need not have bounded exact bit complexity. It is not a finite set of memory states or efficient computation merely because its dimension is finite.
4. **Predictive state:** retain selected future-test probabilities sufficient to recover every permitted future observation-law prediction, updated recursively. Its dimension can be smaller than a belief vector, but requires an actual rank/sufficiency certificate. Counting interaction types or Fourier features supplies none.
5. **Approximate memory:** truncate or approximate filtering/memory while proving a specified finite-horizon output-law error. Requires an error norm, initial-law contract, temperature domain and uniform control. No uniform-in-size or low-temperature forgetting rate has been proved.

“Finite-dimensional” without regularity, precision and update-cost restrictions is not a meaningful efficiency guarantee: arbitrary finite states can be encoded into a single real number.

## 4. Reusable prior and Alexander suppliers

[Littman, Sutton and Singh, Predictive Representations of State, NIPS 2001, Theorem 1 and equations (3)–(4)](https://proceedings.neurips.cc/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf) prove finite-POMDP linear predictive representations bounded by hidden-state count. Their float/reset example distinguishes finite observation windows from recursively retained predictions. A linear PSR refers to linear test prediction; its normalized observation update is generally rational, not a globally linear state update. Finite controls fit the recorded menus; extending algorithms to an uncountable positive-temperature action family requires an explicit argument.

[Shalizi and Crutchfield (2001)](https://arxiv.org/abs/cond-mat/9907176) provide causal-state predictive sufficiency/minimality under their process assumptions. This is not an automatic finite-state or uniform-size bound for the controlled nonstationary cooling experiment. [Li et al. (2015), section II](https://pmc.ncbi.nlm.nih.gov/articles/PMC4644152/) use Mori–Zwanzig to retain memory and fluctuating effects in coarse dynamics; exact projected equations do not establish finite memory support, an autonomous descriptor kernel, or a small simulation algorithm.

The already-existing Alexander suppliers at immutable pin e2502c82ab9a77c00543932f775a71e5374221f7 are particularly relevant:

- [RESULTS.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/RESULTS.md): deterministic coarsest exact representation, distinguishing words and intervention scope.
- [ControlledMemory.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/ControlledMemory.lean): `history_commutes`, `no_finite_suffix_decoder`, `reachable_probe_witness`. Its parity example exactly demonstrates finite recursively stored memory with no uniformly sufficient finite record suffix. It is a stipulated example, not the cation MC.
- [STOCHASTIC.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/STOCHASTIC.md): `exact_iff_all_initial_laws`, joint transcript preservation, and joint-sensor contracts. Crucially, its six-state `no_commuting_profile_kernel` example shows that equality of every future output trace from two microscopic states need not define a commuting stochastic quotient of microscopic states. Do not transfer the deterministic coarsest-quotient theorem blindly to stochastic predictive profiles.

These source bodies were inspected; no compiler was invoked here or new verification claim made. The selected stochastic source labels its approximate transcript-TV bound as proposed/not yet mechanized in that packet. A later supplier might close it, but no fresh build is inferred.

## 5. Correct next proposition for target B and bounded attack plan

Target B records energy/Fourier at each measurement block, SRO at every fifth block, temperature continuation and deterministic block statistics with original tie, threshold and undefined-value conventions. Internal equilibration and measurement gaps consist of many attempts. Unobserved excursions can leave and return to d, so the proof in section 2 cannot simply replace K_T by K_T^m.

**First freeze the actual sampled experiment.** Let P_t be the relevant power or product of K_T between readouts and g_t the time-specific readout. Include block index/schedule phase in bookkeeping. Use the actual initialized law, propagated through equilibration; do not replace it by stationarity. SRO omission means g_t differs between blocks. Preserve the joint history from which all summaries are calculated; accumulated summaries need their own bookkeeping if records are emitted online. A fixed finite run can always retain its whole finite history, which says nothing about uniform memory for arbitrary continuations.

**Finite-suffix target:** for a fixed h, exhibit two positive-probability observed histories under this SAME initialized sampled process, with the same last h observation/control symbols and same current schedule phase, but unequal conditional laws of a specified future B readout. Alternatively prove equality for every such history and every admitted continuation. To prove no finite order, supply witnesses for every h; to refute a uniform size bound, supply an appropriate family of admitted sizes. The A/B point-mass result alone does neither for this contract.

**Latent-predictive target:** define future-test likelihood vectors v_w over microscopic states for the sampled joint observation/control experiment. Their finite-dimensional span is invariant under the appropriate transition/observation operators. Choose a basis and prove recursive update plus all-test prediction, preserving the chosen initial law. A rank bound growing slowly with N, or a certified reduced invariant family, would be a genuine source-specific compression result. A finite test-by-history matrix of rank r supplies a lower bound r for linear predictive representations; it does not alone lower-bound every nonlinear coding. No rank claim for this source is presently proved.

**Practical first attack:** use the original witness to select an added local-environment statistic (e.g. the count of sites with r_ip1=r_ip3=0), then test exact closure rather than assume the statistic suffices. Separately ask whether a recursively updated collection of environment probabilities gives a closed predictive subspace under each recorded block operator. A negative certificate needs only a correct admitted witness or rank minor; a positive statement needs all admitted states/histories and controls. Avoid state-space enumeration as a claimed structural solution.

**Approximation fallback:** specify a finite horizon and seek a uniform conditional one-block predictive discrepancy ≤ε on admitted reachable histories, plus initialization error δ. A coupling argument can then give transcript error at most δ+nε (capped at 1), provided the same observable-history policy and conditional contracts hold. Mixing of hidden states alone is not a filter-forgetting theorem; rare observations and normalization can amplify posterior differences. Empirical fit is not a uniform error certificate.

## 6. Recommended disposition

Keep the new finite-history corollary as scoped hand mathematics attached to the existing one-attempt obstruction, pending review. Select sampled-process predictive-rank/latent-state admission as the meaningful next mathematical gate. Do not advertise a general memory closure, efficient compression, fixed-initializer infinite-order result, synthesized-material prediction or resolution of target B. The strongest immediate reuse is Alexander's precise separation of observation history, retained latent memory, allowed interventions and joint output laws.

## 7. Noise, initialization information and correlated data

The corollary forbids one **history-only** predictor common to the two deterministic initial laws. If the predictor receives the initializer identity or the initial prior as an additional input, its inputs differ and the contradiction does not apply. A belief filter must be initialized with that actual prior, conditioned on any initial measurement; supplying the prior is part of the observation/information contract, not information reconstructed from the descriptor.

Three uncertainties must remain separate:

- **True stochastic dynamics:** random proposals and Metropolis acceptance in the ideal K_T. These already generate a correlated process; “noise” does not imply IID samples.
- **Measurement noise:** the frozen descriptor output is exact mathematical readout. Adding noisy sensors changes the model. For a general joint kernel J_u(x,z,o), predict p(o)=Σ_x,z b(x)J_u(x,z,o), and update b′(z)=Σ_x b(x)J_u(x,z,o)/p(o) when p(o)>0. This preserves next-state/measurement correlation. A simpler transition-times-emission factorization needs a justified conditional-independence assumption. Zero-probability histories may receive arbitrary conventions but cannot serve as positive-probability counterexamples.
- **Model discrepancy:** fitted CE error, omitted physical contributions, unknown calibration or an inaccurate kernel. The filter is exact only relative to its stipulated model. A prior over fixed unknown parameters requires retaining their joint posterior with the state; averaging their prior afresh at each step generally changes the dynamics.

Spatially correlated fields and sequential observations require their actual conditional joint laws. Repeated measurements from one MC trajectory are not independent replicates. For biological sequence data, linkage, shared history and common nuisance parameters likewise require source-specific dependence assumptions; a generic multinomial confidence argument cannot silently replace them. Persistent sensor drift or controller/environmental memory must enter the latent state or a justified joint conditional law.

The finite-state belief formula is an exact existence construction for each fixed finite lattice and known model. Its hidden-state coordinate count grows combinatorially with lattice size; exact coordinates can require unbounded precision. Adding continuous parameters or sensor memory can make the latent carrier nonfinite. None of the above proves an N-uniform dimension, bounded numerical precision, efficient update, stable filtering, or calibrated physical prediction.


## Navigation
[Readable Google document](https://docs.google.com/document/d/15WHhkNcMfuypBWL56dOfPI-gFVPcuHQnmHu-Smh0BmQ/edit)
[Connection index](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
