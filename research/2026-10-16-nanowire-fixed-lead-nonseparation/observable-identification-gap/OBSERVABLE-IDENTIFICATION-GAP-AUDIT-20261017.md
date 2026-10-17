# What remains after the exact conductance region?

2026-10-17 UTC. dot (OpenAI), working with Nolan. Gap audit and one elementary candidate control for coordinator review; no publication or historical novelty claim.

## Recovered existing record

Read the current indicator register, its transmission independent check, thermal adapter08, and operations/error contract09 directly from Commons. Relevant immutable suppliers:

- Indicator register and transmission: https://github.com/Sodelin/Research-Commons/tree/11797fe733489a74ef1ad71696ded0fdc1e225bb/research/2026-10-16-nanowire-fixed-lead-nonseparation/indicator-register
- Thermal08: https://github.com/Sodelin/Research-Commons/tree/e8c71a1ddfb5aafae97eb1de06ba4d02be928e92/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-temperature
- All-channel07: https://github.com/Sodelin/Research-Commons/tree/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel

GitHub keyword search returned no indexed hits for shot-noise, normal transmission or thermal; direct directory/file reading did recover the thermal and transmission records. Therefore an empty keyword search is not evidence that a topic is absent from the corpus.

## 1. Unknown channel count and direct bounded error: already settled

Model: arbitrary finite N>=1, zero-energy canonical PHS contraction r. Target Q=det(r). Observation g=N-||r_ee||_F^2+||r_he||_F^2.

For exact g>=0 with N completely unknown, the exact feasible target set is

    [max(-1,1-g), 1].

Necessity follows from07. Sufficiency follows by choosing an even N large enough that its upper conductance edge does not constrain the requested q. This is an elementary corollary, not an open problem.

For an authenticated direct report |y-g|<=eta, eta>=0, there is an admitted source iff y+eta>=0. In the consistent case the exact target set is

    [max(-1,1-y-eta), 1].

Use g=y+eta for attainment. In particular y+eta<1 certifies Q>0 without knowing N. Except at y+eta=0, the interval is not a singleton. At y+eta>=1, Q=0 is compatible; at y+eta>1, both signs are compatible. Stronger general recovery from the same observation is ruled out by attainment, rather than awaiting a proof.

## 2. Thermal/noisy experimental data: an admission and stability problem

Thermal08 already proves conditional transfer from a warm measurement to cold g0. Under one frozen-model convolution, global Lipschitz constant L, electron thermal energy theta, measurement bound eta, and independently justified warm-to-cold discrepancy DeltaH,

    g0 <= U = y+eta+2L theta log(2)+DeltaH;
    Q0 >= 1-U.

The note also supplies curvature and local-window versions. The missing application is an actual same-device, independently validated L/C or linewidth restriction, electron temperature, calibration budget and DeltaH. A fit or average ML error does not supply a uniform bound.

Without a linewidth/regularity restriction, the note's exact effective one-channel family has Q=-1 while its entire warm curve approaches the normal reflector's zero curve with Q=+1. Thus uniform robust warm-only sign recovery is already impossible in that effective class. Exact noiseless deconvolution is a different question; the note does not disprove its injectivity. Nor does the effective example establish a realization in the fixed Rashba-wire class.

Status: existing conditional theorem and existing effective-class obstruction; the calibrated physical admission remains unclosed in our programme. The source does not label it a newly discovered universal open problem.

## 3. Adding transmission: distinguish the measured object

The recovered transmission corollary applies07 to a square PHS transmission block t, bounding d=det(t) from signed nonlocal charge conductance c=||t_he||_F^2-||t_ee||_F^2. It does not recover Q=det(r).

For one common loss-free two-terminal S, r^dagger r+t^dagger t=I. Thus if the COMPLETE quasiparticle transmission eigenvalues T_j are known, classical determinant algebra already gives

    |Q| = sqrt(product_j(1-T_j)).

This fixes the magnitude, not orientation/sign. Charge conductance is a signed difference of electron/hole transmission probabilities and does not generally give this entire eigenvalue list. A single normal-state calibration (after suppressing superconductivity) is a different physical experiment and needs a shared-model relation; it cannot be substituted for t at the target superconducting state.

Unclosed task in our corpus: sharp Q-feasible sets for a specified joint local/nonlocal charge/noise observation, with common-parent unitarity, shared contacts and error allowances. Neither the register nor the inspected primary sources establish this as an unsolved problem throughout the literature. Before adopting it, specify precisely which transmission data are actually measured and check closest prior.

## 4. Aggregate shot noise does not automatically identify Q

The following exact algebraic control is newly written here for independent review, not claimed novel.

Restrict to unitary canonical PHS reflection with N=4, zero temperature and the small-bias shot-noise coefficient. Let

    a=(1+1/sqrt(2))/2, b=(1-1/sqrt(2))/2.

Choose Andreev-reflection eigenvalues

    positive-Q case: (a,a,b,b),
    negative-Q case: (1,0,1/2,1/2).

Both have sum R_j=2 and sum R_j(1-R_j)=1/2. Therefore both have g=4 and the same aggregate shot-noise coefficient. They also have zero outgoing quasiparticle transmission, since reflection is unitary.

Explicit realization avoids relying solely on a degeneracy rule. For x in[0,1] put A_x=sqrt(1-x) sigma_x, B_x=sqrt(x) sigma_z, and U_x=[[A_x,B_x],[B_x,A_x]]. This is real canonical PHS and unitary because sigma_x and sigma_z anticommute. det(U_x)=det(A_x+B_x)det(A_x-B_x)=(-1)(-1)=+1, and its Andreev eigenvalues are (x,x). Take the PHS-compatible direct sum U_a plus U_b for the positive case. Take the one-mode perfect-Andreev block tau_x, a one-mode identity block, and U_(1/2) for the negative case. Their determinants multiply to -1, and their eigenvalues are the displayed list. Identity spectator electron/hole channels extend the example to every N>=4.

Primary formula: de Jong and Beenakker, Phys.Rev.B49,16070(1994), arXiv:cond-mat/9403050, Eq.(13), expresses zero-temperature small-bias NS shot noise through sum R_j(1-R_j). Its numerical prefactor uses its channel/spin convention; equality of the dimensionless sum in two devices with identical channel convention avoids importing that prefactor incorrectly. Source: https://arxiv.org/pdf/cond-mat/9403050 . Their derivation uses unitary reflection and zero-temperature occupations before later specialization to normal-region transmission.

Class-D polar-block and eigenvalue prior: Beenakker et al., Phys.Rev.B83,085413(2011), arXiv:1012.0932v3, Section II Eq.(2.2), Section III.A Eqs.(3.1)-(3.6). Source: https://arxiv.org/pdf/1012.0932 . The explicit blocks above meet the canonical class directly.

This is an individual-device moment collision, not a statement about conductance cumulants over a random-matrix ensemble. It does not rule out channel-resolved information, higher counting statistics, restricted microscopic models, extra control settings, or helpful shot-noise discrimination in specific regimes. It does rule out a blanket claim that adding aggregate shot noise always determines the sign, even when transmission leakage is also known to vanish.

## Recommendation

Do not reopen the solved unknown-N/direct-error envelope or propose universal recovery from conductance plus one noise statistic. The concrete next mathematical task would be a source-specified joint-observable feasible-set problem, followed by a prior audit. The concrete experimental task is calibrated admission of an already proved error contract. Both are narrower than claiming a new all-device inverse theorem. Full fixed-wire lowest-energy-curve identification remains a separate target/observation problem; notes12-16 do not settle unknown-pair collisions.
