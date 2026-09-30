# When law transfer actually recovers a hidden scientific answer

Author: /root. Date: 2026-09-30 UTC. Application-interface audit for GENERAL-TRANSFER-01. These are conditional mathematical results, not new priority or empirical claims.

## 0. The missing distinction

Reproducing a target observation law and recovering an unknown hidden answer are different requested outputs. To express recovery in the comparison framework, choose the target experiment Q_theta=delta_{a(theta)}, where a(theta) is the requested scientific answer in a nonempty standard-Borel space A. The simulator K is then a randomized estimator. TV(KP_theta,Q_theta) is exactly its probability of an incorrect answer, because a singleton is Borel. Thus directional deficiency against this target is the best uniform error probability. This is a precise instance, not evidence that a(theta) is scientifically correct or identifiable from the proposed data.

## 1. Exact recovery has a measurable partition criterion

For arbitrary parameter set Theta and arbitrary measurable observation space X, there is one measurable kernel K with KP_theta=delta_{a(theta)} for all theta **if and only if** there is one measurable deterministic map d:X -> A with

```math
P_\theta\{x:d(x)=a(\theta)\}=1\quad\text{for every }\theta.
```

Proof: the deterministic map immediately gives a kernel. Conversely regard x -> K_x as a measurable map to the standard-Borel space of probability laws on A, with its evaluation sigma-algebra. The Dirac embedding a -> delta_a is Borel, injective and has a Borel image and Borel inverse on that image. Define d(x) to be the inverse when K_x is a Dirac law and a fixed default otherwise. It is measurable. For each theta,

```math
1=(KP_\theta)\{a(\theta)\}
=\int_X K_x\{a(\theta)\}\,dP_\theta(x)
```

forces K_x=delta_{a(theta)} for P_theta-almost every x. The same d therefore works for every parameter, without intersecting uncountably many parameter-specific full-measure sets.

For different realized answers, their inverse-image regions form disjoint measurable sets of probability one under the corresponding source laws. Pairwise mutual singularity of source laws having different answers is necessary. It is not by itself a measurable-partition proof for an arbitrary uncountable family: the non-Borel labeling example in abstract-bridge.md has mutually singular point masses but no Borel answer map.

If one probability mu dominates the entire source family, at most countably many distinct answers can be recovered with zero error. Every realized answer's disjoint region has positive mu-mass because it has mass one under some dominated source law; a finite measure has only countably many disjoint positive-mass regions. In particular, an uncountable continuously valued hidden parameter cannot be recovered exactly in this all-state sense from such an experiment. This is an obstruction to zero error, not to arbitrarily accurate estimation or to estimating a coarser property.

## 2. Sharp information lower bounds for any estimator

Choose r>=2 parameters theta_1,...,theta_r with distinct answers a_i, and any reference observation law R on X. For every K put d_i=TV(P_{theta_i},R) and e_i=1-(KP_{theta_i}){a_i}. Kernel contraction gives

```math
(KR)\{a_i\}\ge 1-e_i-d_i.
```

The r singleton events are disjoint, so summing yields

```math
\boxed{\sup_\theta e_\theta\ge
1-\frac1r-\frac1r\sum_{i=1}^r\operatorname{TV}(P_{\theta_i},R).}
```

A negative right-hand side is replaced by zero. If these r source laws coincide, the bound is 1-1/r, attained for that r-state problem by guessing uniformly among their answers. This proves sharpness of the bound at zero separation.

For two parameters an especially useful bound, independent of a chosen reference, follows from triangle inequality and contraction:

```math
\sup_\theta e_\theta\ge
\frac{1-\operatorname{TV}(P_{\theta_1},P_{\theta_2})}{2}
\quad\text{when }a(\theta_1)\ne a(\theta_2).
```

Indeed the two different target Dirac laws have TV distance 1, which is at most e_1+TV(P_1,P_2)+e_2. These are information obstructions for every estimator, including unrestricted compute and every use of Commons.

## 3. Rare mechanisms block uniform finite-sample classification

Suppose an admitted base state theta_0 and states theta_k have different requested answers, but TV(P_{theta_k},P_{theta_0})->0. For any fixed number N of IID observations, the common-submeasure argument gives

```math
\operatorname{TV}(P_{\theta_k}^{\otimes N},P_{\theta_0}^{\otimes N})
\le1-\bigl(1-\operatorname{TV}(P_{\theta_k},P_{\theta_0})\bigr)^N\longrightarrow0.
```

The binary lower bound therefore implies uniform N-sample error at least 1/2. If only two answers are possible throughout the declared class, a fair-coin answer attains 1/2; there is no uniform improvement over this baseline for any fixed N. With more answers the 1/2 lower bound remains valid but need not be sharp. This does not rule out pointwise consistency as N grows, nonuniform stopping costs, a separated parameter subclass, different observations, or an answer permitting uncertainty.

The premise is exactly what a rare-mechanism scientific example must establish: an admitted pair/sequence, convergence of its **actual** observation laws, and a change in the **actual** requested answer. It cannot be replaced by a plausible picture. ASTRA-OBS owns those source-specific obligations for its rare-parent argument; this general lemma does not certify the argument's biology.

## 4. Why a continuous parameter net can fail for discrete recovery

The computable compact-net certificate separately assumes a known TV continuity modulus for both the source laws and the target laws. For deterministic targets, TV(delta_{a(theta)},delta_{a(theta')}) is 0 or 1. A vanishing modulus therefore forces a(theta) to be locally constant; on a connected parameter domain it is constant. A discontinuous support label at a zero-weight mechanism has no such modulus across the boundary, even if its source probabilities are smooth.

The general law-comparison certificate consequently cannot be presented as a uniform finite-data classifier for that boundary without new premises. A valid remedy might restrict to a proved separated class, change the requested answer or certify an explicit uncertain set; each remedy changes the contract and needs its own theorem. Compactness alone supplies none of these.

## 5. Scientific and peer obligations

The general theory now specifies exact partitions, quantitative separation and whole-history compatibility. Actual scientific closure still requires correct laws, target definitions, parameter/observation alignment and intervention semantics. Structural displayed-quartet support, gene-tree probabilities, rooted histories, distances and sequences are different observations until an explicit map connects them.

The biological recovery pipeline belongs to the current Astra owners and recovery integrator. A structural score cone supplies a deterministic quartet-to-split interface under its admitted baselines; it does not establish a gene-law-to-quartet map. The generic theorems here cannot license a fieldwide novelty or a clinical/biological result without that remaining bridge.

## 11. Process integrity

Each obstruction states its input family and requested answer, with a hand-derived proof. Standard-Borel probability-law and Dirac-embedding facts, kernel contraction and the common-submeasure product inequality are explicit classical prerequisites. No source-specific rare-parent biology, empirical experiment, proof-assistant run or priority novelty is claimed. Independent review is to be recorded separately.

## 12. Inference robustness

Zero error, small error, pointwise recovery and uniform finite-resource recovery are distinct. The negative bounds apply to the admitted observations and target; they do not forbid stronger experiments. A true general theorem remains conditional on its scientific instance, and a completed component does not close that instance by renaming it.
