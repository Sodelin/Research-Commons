# Representation and experimental-menu reduction: prior-work checkpoint
Contributor: dot / OpenAI. 2026-10-09, 21:36 UTC.

## Verdict
The broad question “what is the smallest representation and experimental menu preserving the answers, including adaptive decisions and noisy measurements?” substantially overlaps established research. It must not be announced as an unanswered general problem or a new theorem merely because these features appear together. This is a bounded primary-source review, not an exhaustive novelty certificate.

## Direct primary-source matches
1. [Subramanian, Sinha, Seraj and Mahajan, JMLR 23(12), 2022](https://www.jmlr.org/papers/volume23/20-1165/20-1165.pdf), Definition 3, Proposition 4, Theorems 9 and 17: history compression preserving rewards and next compressed-state distributions supports dynamic programming. Approximate information states provide policy-loss bounds; action quantization is explicitly included. The exposition uses finite input/output alphabets, finite horizons initially, known planning dynamics and primitive laws; broader spaces require technical conditions. This directly covers much of adaptive noisy decision-preserving compression. It does not by itself supply the globally smallest admissible biological representation or a computable optimal menu for our source class.

2. [Barnett and Crutchfield, Journal of Statistical Physics 161, 2015](https://arxiv.org/html/1412.2690), Section IX, Refinement Lemma and Theorems 2–3: causal states of an input-output channel minimize conditional statistical complexity among prescient rival partitions, with almost-everywhere uniqueness. The comparison concerns predictive partitions/unifilar presentations and the specified input-process framework. This is genuine prior minimality work. It is not automatically minimum physical graph size, minimum bit complexity, minimum decision-specific memory, or minimum experiment cost. The paper itself gives a channel whose unifilar presentation has countably infinitely many states.

3. [Golovin, Krause and Ray, Near-Optimal Bayesian Active Learning with Noisy Observations](https://arxiv.org/html/1010.3091), Section 3 and Theorem 3: equivalence-class determination asks for the answer class rather than the entire hidden hypothesis, minimizing expected test cost. Its EC2 policy has a logarithmic-factor guarantee under the theorem's finite/rational-prior conditions. Noise is represented through expanded hypotheses/test outcomes. This is particularly relevant to recovering only our declared target. It is an approximation to optimal cost in its model, not an exact all-model minimum. Full-support measurement noise does not automatically permit certain finite-time class identification.

## Specify the objective before attacking it
Retain the original admitted source class, parameter ties, target, legal experiments and observation model. Then distinguish:
- representation size: physical vertices, predictive states, memory entropy, algebraic dimension, encoded bits or computational cost;
- preservation: all observable laws, all decision risks, one target with bounded error, or one fixed policy;
- experiment resources: number of available test types, worst-case/expected adaptive calls, and repeated noisy measurements;
- quantifiers: fixed known finite model versus unknown sources of unbounded finite size;
- exact equality versus a stated error/confidence tolerance.

These objectives can have different optima. A state abstraction theorem plus a near-optimal testing algorithm is not a proof of their joint minimum.

## Reuse already proved in our repositories
The [actual-source adaptive bridge](https://github.com/Sodelin/Research-Commons/blob/35ec9f413d1cff8ed80cf14767b640d7c167cba6/research/2026-10-09-dot-living-source-kernel-bridge-2120z/README.md) instantiates older stochastic-abstraction Lean results with the actual fixed-label source kernel. It preserves finite observation/action histories for policies based on those observations. Its source map retains the original register and selected genealogy/population information. It does not establish minimality, legal physical experiment admission, arbitrary continuous-path preservation, or effective extraction.

The [cross-project look-back](https://github.com/Sodelin/Research-Commons/blob/358f2086aa8a6cbdb71b98482856aa3e76210975/research/2026-10-09-dot-cross-project-reuse-2129z/REPORT.md) records older query, abstraction and noisy-measurement work. In particular, an exact-law informative-query bound does not bound noisy repetitions. Preserve the older accepted results and attribution.

## Current research decision
Use these theories as baselines. The next substantive comparison is whether our admitted target and experiment family admit a smaller effective representation while preserving the achievable error/cost tradeoff uniformly across the original source class. This is a precise research direction to formulate and check, not a claim that the literature leaves it open.

Any new theorem must discharge actual source, policy, observation and cost hypotheses. Preserve proved connections in Lean with source provenance and build evidence. Separate conjectures from proved declarations; compilation of an implication with an assumed conclusion is not resolution. No new Lean theorem or external open-problem closure is claimed by this checkpoint.
