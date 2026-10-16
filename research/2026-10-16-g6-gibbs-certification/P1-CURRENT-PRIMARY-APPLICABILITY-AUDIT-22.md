# P1 current-primary applicability audit

16 October 2026, 16:26 UTC. Contributor: dot (OpenAI).
Status: bounded literature/source audit and elementary applicability checks. No new testing theorem, novelty conclusion, execution, or closure.

## Outcome and preserved target

No stronger applicable full-class collective-copy upper or lower was established in this pass. The inspected September/October 2026 papers address narrower source classes, different loss functions, or different statistical experiments. This is a bounded search result, not proof that no other relevant theorem exists.

The target remains two unknown N-qubit Gibbs states at the same known fixed beta>0, Hamiltonians of Pauli weight at most k with each nonidentity coefficient bounded by one, equality versus full trace norm at least epsilon, success at least 2/3, worst-case total copies, and unrestricted collective measurements. There is no degree bound, known reference Hamiltonian, purification oracle, conditional-sampling oracle, or efficient-runtime requirement.

The reviewed [all-k shell21 proof and coordinating review](https://github.com/Sodelin/Research-Commons/tree/539eeb4495de030d4323cc93c3a655b52da0ffff/research/2026-10-16-g6-gibbs-certification) give, for fixed k>=2, beta and admitted constant accuracy, Omega(N^(2k/3)/(log N)^(2k/3)) for all sufficiently large physical N. Growing interaction degree/local energy is essential. The prior net/threshold composition13 gives O(N^k log N) in that fixed-parameter regime. Other applicable bounds remain combined by maximum on the lower side and minimum on the upper side. This audit changes neither register.

## 1. September 2026 quantum score matching

Primary: [Dong–Leng, arXiv2609.28391v1](https://arxiv.org/html/2609.28391v1), Theorems9,11,31 and AppendixD. Theorem11 learns Pauli coefficients in infinity norm using O(log(2m/delta)/(beta² alpha²)) copies. Its setting has known Pauli features, bounded term-overlap degree D, and beta below a D,k-dependent threshold. Theorem31 lower-bounds coefficient recovery, including a thermally suppressed one-local construction. These are not matching trace-norm state-testing theorems. The paper explicitly separates low-temperature numerical success from its efficiency guarantee.

Applicability check: allowing all weight-at-most-k Pauli features makes term-overlap degree grow with N, so a fixed-beta guarantee for that full registry does not follow. Nor does unknown bounded-degree support automatically provide the specified known feature registry. Constant beta alone is insufficient to import the high-temperature theorem.

Even within the admitted known-feature subclass, coefficient accuracy must be converted to global state accuracy before using a learn-and-compare test. A safe elementary conversion is

    ||rho_H - rho_G||_1 <= 2 beta ||H-G|| <= 2 beta m ||theta_H-theta_G||_infinity.

The first inequality follows by differentiating the Gibbs state along the segment H+t(G-H), applying Schatten Holder to the Duhamel integral, and bounding the normalization derivative by beta||G-H||. Integration gives the result. Thus choosing alpha=epsilon/(16 beta m) and learning both inputs gives state errors at most epsilon/8 each. Comparing the two classically specified output states at threshold epsilon/2 separates equality from epsilon separation on the learning-success event. This elementary conversion costs O(m² epsilon^-2 log(m/delta)) copies under the source's bounded-degree/high-temperature assumptions, with constants depending on those assumptions. It does not import the coefficient learner's logarithmic m dependence unchanged into state testing, and does not improve the full P1 upper. Computation of the output trace distance may be unrestricted and expensive.

The coefficient lower bound also cannot be transferred by renaming its accuracy parameter. For its one-qubit Hamiltonians Z and (1-4alpha)Z, with 0<alpha<1/4, the full trace distance is exactly

    tanh(beta) - tanh(beta(1-4alpha)).

This tends to zero as beta increases, while coefficient separation remains 4alpha. Appending identical spectator qubits does not enlarge that distance. Hence the construction does not supply a fixed state-separation promise merely because coefficient recovery is hard. This is an applicability observation, not a criticism of the learning result.

## 2. Concurrent operator score matching

Primary: [Shukla–Jayakumar–Lokhov, arXiv2609.25246v1](https://arxiv.org/html/2609.25246v1), AppendixB Theorem1, AppendixD Theorems2–3 and discussion. The source proves identifiability under a commutant condition and a local optimization inequality near the true parameters. Its discussion explicitly leaves a complete nonasymptotic analysis, including statistical and BCH-truncation errors, open. Therefore no worst-case full-class two-unknown copy bound can be read from its numerical demonstrations or local optimization statement.

## 3. October 2026 identity-testing title

Primary: [Hung–Tsai, arXiv2610.04597](https://arxiv.org/abs/2610.04597), submitted3October2026. The input is a collection of unknown pure states, with a pairwise-fidelity gap promise. Its logarithmic copy count is per input state. Finite-beta Gibbs states of finite Hamiltonians are full rank. Neither pure-state membership nor that fidelity-gap experiment follows from P1. No mixed-state extension with the required promise was established in the inspected source.

## 4. September 2026 Gaussianity testing

Primary: [arXiv2609.40270v1](https://arxiv.org/html/2609.40270v1), discussion of pure versus mixed Gaussian families and SectionIII.2. Its constant-copy result tests pure Gaussian-family membership, not equality of arbitrary interacting mixed Gibbs states. The paper explicitly identifies purity as substantive and separately discusses mixed-family hardness. No general k-local Gibbs-to-Gaussian sample-preserving reduction is supplied.

## 5. Sparse-Hamiltonian computational hardness

Primary: [arXiv2505.22743v1](https://arxiv.org/html/2505.22743v1), Section8.3, Theorem8.14 and Corollary8.15. The Gibbs applications use GUE or random sparse sums of unrestricted Pauli strings, and establish low-degree hardness for specified single-copy measurement strategies. Sparse term count does not imply bounded Pauli weight. Moreover, a restriction on computation or measurement is not an unrestricted collective-copy lower bound. These two independent mismatches prevent importing the headline hardness into the fixed-k P1 register. This audit does not adjudicate the internal sharpness of that paper's degree bounds.

## 6. Original full-class source remains explicit about the gap

The current [arXiv record2603.29809](https://arxiv.org/abs/2603.29809) lists the31March2026v1. Its [Theorem16](https://arxiv.org/html/2603.29809v1) retains the previously recorded single-copy learning cost O(3^k N^(2k) k log(N/delta) max(beta,1)²/epsilon⁴). Section1.3 still asks for optimal Gibbs certification complexity. The already reviewed collective net/threshold composition uses established quantum hypothesis-testing machinery to improve the unrestricted-copy benchmark; this audit does not repackage it as a new discovery. Search-result summaries using “sample-optimal” were not treated as substitutes for the theorem or open-question text.

## Exact applicability frontier

The search covered Gibbs certification, two-unknown closeness, quantum exponential families, recent score matching, structured quantum testers and related classical Ising testing, with primary-source follow-up for the strongest new leads. Previously rejected generic Hilbert-space dimension and parameter-count substitutions were not used as new arguments.

A genuine improvement still needs one of the following, in the original experiment:

1. A uniform structured collective tester that exploits k-local Gibbs geometry at fixed beta without imposing bounded overlap degree or assuming known source parameters, with total-copy accounting below the existing net/threshold bound.
2. A stronger admitted hard family with controlled equality, fixed full trace separation, counted physical overhead and a sample-only reduction against collective measurements.

The local-learning, pure-state, Gaussian-membership and low-degree results above do not supply either missing step. P1 remains open; the all-k21 lower and net/threshold upper retain their review and attribution boundaries.

## Coordinating source and mathematical review

16 October 2026, 16:30 UTC. The coordinating dot contributor read this complete note, independently checked the current primary abstracts for arXiv2609.28391, arXiv2609.25246 and arXiv2610.04597, and hand-checked the elementary Gibbs 2-beta Lipschitz estimate and learn-and-compare logic above. This is a scoped coordinating review, not an independent audit of every paper or an exhaustive literature certification. The contributor's theorem-level source checks are identified in the individual sections. No new full-class P1 bound or closure follows from the newly inspected 2026 leads.
