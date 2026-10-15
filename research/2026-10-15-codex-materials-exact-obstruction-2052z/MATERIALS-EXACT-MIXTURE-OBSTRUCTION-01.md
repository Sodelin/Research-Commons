# Exact mixed-kernel obstruction for the published YBaMnFeO5 descriptor family

15 October 2026. Contributor: existing materials lane 2, transfer/counterexample owner. Revision 4 incorporates Root's authoritative 20:46 UTC base-model freeze and exact source binary64 lifts; the geometric hand argument is unchanged. Supersedes r1-r3 only on contract/arithmetic wording. Status: HAND-DERIVED EXACT ARGUMENT, WITH BOUNDED EXACT NAMED-WITNESS CHECK; independent mathematical cross-review remains pending. No model import/execution, state-space search, random draw, MC trial, solver, Lean invocation or new worker. This is a result packet under the existing shared contract 02, not a replacement contract or new research lane. Mathematical novelty is unassessed.

## Exact model and inherited sources

The complete pinned mc_ce.py was fetched and read: repository spicylemonade/compensated-magnet-ledger, commit 45551de5fac4e69de3e03c420b31abb335d73ef4, materials/YBaMnFeO5/cation_order_cluster_expansion/mc_ce.py; 7,455 bytes, SHA256 0285d2a76406b344ada4b7bb602fe9ff48b5b79ac3cfffb6453c136330d91048, Git blob 84c8657d45674e4da7a7c2da5b010521ff3fbafc. No import or execution occurred.

The complete accepted G2UniversalTransitionCriterion.lean was read at Commons commit e85b58325b4541343630296ceb003029ed7205a5: 5,433 bytes, SHA256 ae8d8a1698be9810533bb4b6db5e8184882d635e2acc0ffe160ffc8e50dfd5a5. Its row orientation is A*P=P*B. MC uses discrete kernels as pulses and products, not a continuous-time generator.

The COMPLETE existing lane3 contract 02 was read and independently authenticated: Commons commit 7fda64d20e107af44385b789e26663ba1305d73b, research/2026-10-15-astra-materials-kernel-adapter-2035z/MATERIALS-DISCRETE-QUOTIENT-CONTRACT-02.md; 12,156 bytes, SHA256 ebf4239edd0cac58df17b9dd308ba5af2684c31b7a43a6fb8eff96fa7f586db6. The prior-lane source/fit/schedule/literature audit is reused with attribution, not duplicated.

## Short comparison, reusing the shared contract

| Route | Fit and preservation | Missing bridge/error; Lean readiness |
| --- | --- | --- |
| Schrieffer-Wolff | Gapped Hermitian spectral-sector reduction, HJ=JH_eff, with transported observables and controls. | The cation CE supplies no microscopic Hamiltonian, certified gap or truncation/observable error. Existing quantum hand bridge is inherited; no materials quantum adapter is selected. |
| Cluster expansion and lumpability | Direct fit to this MC source. Pair descriptors encode the fitted energy; kernel intertwining would preserve descriptor path laws. | Energy factoring alone does not imply Markov closure. The exact instance obstruction below attacks that missing premise. Existing compiled G2 product composition is reusable, not newly authored here. |
| Mori-Zwanzig | Projection retaining memory/fluctuating-force terms when hidden geometry matters. | Exact memory equations do not establish a small memoryless state. Finite augmentation or a controlled memory approximation needs its own initial-law/error contract; no separate implementation is opened. |

## Agreement/correction on the five freeze fields

1. **Descriptor.** Agree with full D9F in contract 02; incorporate Nolan's nested comparison D8 -> D9 -> D9F. D8 comprises the eight active pair correlations; D9 adds the ip4 correlation; D9F adds EVERY retained labelled Fourier amplitude in source order. The witness below has equal D9F, so it also addresses D9 and D8. ip4 is the stated far-neighbour class, not node strength, and no coupling is added.
2. **Lattices.** Preserve the complete published assertion over 8^3, 12^3, 16^3. The nontrivial kernel obstruction is at the ACTUAL published/default 12^3 lattice and extends to L divisible by 12, even Lz>=6. This family has no offset aliases/self-loops. It refutes a universal assertion covering all published sizes; it does not assert the same dynamic obstruction at 8^3 or 16^3. The full labelled-array factoring obstruction applies at every admitted nonempty balanced lattice.
3. **Arithmetic and coefficients, Root 20:46 freeze.** Select exact rational lifts of the SOURCE binary64 main-fit couplings, obtained with as_integer_ratio, with ip4=0. Displayed decimal rationals are NOT the base parameters. The same-pin torder result was fetched solely to close this exact binding: 58,992 bytes/SHA256 cfd733fdda3dced71b29bf1f74240ac7cb795546a3606e0b851afcf57c556ecc, Git blob 05b79de00d1f0ebda2700927320f9c7e152ace77; only its key/classes/V fields were used. The exact ratio map is in EXACT-BINARY64-SOURCE-LIFTS-CHECK-r2.json. The proof also holds for every finite real coupling vector as an explicit mathematical strengthening, not a substitution of a different fit. No bit-exact floating/PRNG equivalence is asserted.
4. **Temperature and controls, Root 20:46 freeze.** The BASE kernel is the published half-local/half-arbitrary mixture. Pure local/arbitrary controls below are OPTIONAL strengthened mathematics, not claimed separately published. All finite T>0 is a labelled ideal mathematical family containing the recorded positive menus; no claim all temperatures were simulated. Local means ONLY the first four in-plane ip1 neighbours. Equal-spin proposals and rejections remain self loops. The actual mixture obstruction is proved directly; it is not inferred from a component-only failure.
5. **Target, resolved by Root at 20:44 UTC.** Select claim B: the FULL JOINT CHRONOLOGICAL LAW of required energy, all NINE pair-SRO and Fourier-order readouts, and their defined block estimators, ties and undefined cases. The final labelled array is NOT an observed output for B. Hidden labelled configurations and update history still supply every admitted future temperature program. This is explicit observable selection, not full API equivalence. Record claim A separately: including the final labelled array forces injectivity; that straightforward observation is not a new materials discovery. The exact kernel obstruction below refutes the requested scientific descriptor quotient without relying on array exposure.

The shared source contract is contract 02 with Root's 20:44 target-B resolution and authoritative 20:46 base-model freeze: mixture, documented sizes 8/12/16, source binary64 rational lifts, and nested D8/D9/D9F (D9F is contract 02's D_aug). 

Source-provided default initialization is uniform on balanced configurations, so each named witness has positive initial probability. The selected strong-lumpability/G2 claim is universal in admitted source states; no weak-lumpability inference for a special initial law is substituted.

The selected instance is the ideal independent-draw Markov chain with exact real Fourier amplitudes and Metropolis probabilities. Literal seeded NumPy/Numba replay, floating phase roundoff, and reseeding schedules are not verified by this source-reading adapter. Exact phase/amplitude semantics must remain explicit in any later formal adapter.

## Configurations and equality of the full augmented descriptor

Let L=12m (m>=1), even Lz>=6, N=L^2 Lz, coordinates as in build. Define periodic subsets of Z/12Z

    A={0,1,4,6}, B={0,1,3,7},
    a_X(u)=+1 if u mod 12 is in X, and -1 otherwise,
    sigma_X(u,v,K)=a_X(u)*(-1)^K.

Both configurations are exactly 50/50 because Lz is even. They differ as labelled arrays. They are valid states at L=Lz=12, with no special start outside the intended sector.

These are classical homometric cyclic sets; no novelty of homometry or generic lumpability is claimed. The six unordered pairs in EACH of A and B have circular distances 1,2,3,4,5,6 exactly once. Thus their periodic indicator autocorrelations agree at every displacement. For the spins a_X, the length-12 autocorrelation is 12 at displacement 0, 4 at displacement 6, and 0 at all other displacements. This proves equality of every pair-class sum, with the implemented directed multiplicities and factor 1/2. In source CLS order the common vector is

    (S_ip1,S_ap,S_Y,S_ip2,S_apd,S_Yd,S_ip3,S_c2,S_ip4)
      =(N,-N/2,-N/2,0,-N,-N,N,N,0).

Every retained Fourier amplitude also agrees. The only nonzero source modes (qu,qv,qK) are

    (0,0,1): 1/3,
    (0.5,0,1): sqrt(2)/6,
    (1,0,1): 1/3.

All other retained amplitudes vanish; omitted half modes remain omitted according to make_phases. This follows either from the common autocorrelation or directly from sums over v,K and the period-12 sequence. For example, the two half-frequency sums are 2(1+i) and 2(1-i), and the pi sums are +4 and -4. Equality is for amplitudes, as in the source; complex Fourier phases would be a stronger descriptor. Therefore D9F(sigma_A)=D9F(sigma_B), not just D8 or D9.

## Exact field lemma

For c=ip1 or ip3 let r_c(i)=sigma_i*sum_{j in class-c neighbour entries of i} sigma_j. For these two classes each row has four unit-weight neighbours and the graph is reciprocal. For an unlike swap at i,j, with m_c(i,j) the number of class-c entries from i to j,

    Delta S_c = -2*r_c(i)-2*r_c(j)-4*m_c(i,j).

This is obtained by flipping both spins in the half-directed sum; the mutual edge correction is essential. For the striped states,

    r_1(u)=2+a(u)*(a(u-1)+a(u+1)),
    r_3(u)=2+a(u)*(a(u-2)+a(u+2)).

Both are in {0,2,4}, independent of v,K. The complete hand-derived period table is:

| u | A r1 | A r3 | B r1 | B r3 |
|---|---:|---:|---:|---:|
|0|2|0|2|0|
|1|2|0|2|2|
|2|2|0|0|2|
|3|2|2|0|2|
|4|0|2|2|4|
|5|0|4|4|0|
|6|0|2|2|4|
|7|2|4|0|0|
|8|4|2|2|4|
|9|4|4|4|2|
|10|4|2|4|2|
|11|2|2|2|2|

In A there is NO site with r1=r3=0. Therefore no accepted unlike swap whatsoever can leave BOTH S_ip1 and S_ip3 unchanged. This includes arbitrary swaps; all terms in the lemma are nonnegative before the leading minus signs.

## Actual half-mixture and pure arbitrary: one specified destination fibre

In B choose i=(7,0,0), j=(7,0,1), an unlike pair across Y. Let z_B be B with these two spins exchanged and set y_B=D9F(z_B), an EXACT destination descriptor, including all its Fourier amplitudes. Then

    Delta S_ip1=Delta S_ip3=0, Delta S_c2=-8,
    (Delta S_ip1,Delta S_ap,Delta S_Y,Delta S_ip2,
     Delta S_apd,Delta S_Yd,Delta S_ip3,Delta S_c2,Delta S_ip4)
      =(0,4,0,16,0,0,0,-8,32).

In particular y_B differs from the common starting descriptor. The field lemma proves

    K_A(sigma_A, D9F^{-1}{y_B})=0

for pure arbitrary AND the implemented mixture, for every finite V and T>0: a rejected/equal-spin proposal remains at the starting descriptor, while every accepted unlike A proposal changes S_ip1 or S_ip3.

Write alpha_T(d)=1 for d<=0 and exp(-d/(KB*T)) otherwise. B reaches y_B through each of the two ordered proposals (i,j),(j,i). For pure arbitrary its fibre mass is at least 2*alpha_T(d_B)/N^2; for the implemented 50/50 mixture it is at least alpha_T(d_B)/N^2, where

    d_B=4*V_ap+16*V_ip2-8*V_c2+32*V_ip4.

These bounds are STRICTLY POSITIVE for every finite real V and finite T>0. At the selected exact binary64-lifted fit, ip4=0 and d_B=41128429432628793/281474976710656 meV, STRICTLY POSITIVE (approximately 146.11753383288143; approximation is not used in the proof). Thus this is an exact source-admitted SAME-D9F/SPECIFIED-FIBRE obstruction at the fitted model, throughout every positive recorded temperature and the all-positive-T extension. There is no cancellation between the component kernels: the A fibre mass is exactly zero and the B arbitrary contribution is positive. For a mixture with local weight p<1 the lower bound is 2*(1-p)*alpha_T(d_B)/N^2; only p=1 needs the following separate argument.

## Pure local component: a different specified destination fibre

In A swap i=(1,0,0) with j=(2,0,0). Let z_A be the result and y_A=D9F(z_A). The field table gives Delta S_ip1=-12 and Delta S_ip3=0, so y_A is different from the starting descriptor.

Every unlike local B proposal is a horizontal-u boundary; vertical-v proposals have equal spins. The six u-boundaries per period are u=1,2,3,6,7,11, and their Delta S_ip3 values are respectively -8,-8,-12,-8,-8,-4. Hence B cannot reach y_A by an accepted local swap or a self loop:

    K_local(sigma_B, D9F^{-1}{y_A})=0,
    K_local(sigma_A, D9F^{-1}{y_A})
       >= alpha_T(d_A)/(2*N) > 0.

The two ordered local proposals supply the factor 2/(4N). Here

    d_A=-12*V_ip1+4*V_ap+4*V_Y+8*V_apd+8*V_Yd-8*V_c2+16*V_ip4.

At the selected exact binary64-lifted fit d_A=-560975364936605/17592186044416 meV, STRICTLY NEGATIVE, so acceptance is one for every T>0. The proof also holds for arbitrary finite real couplings by strict positivity of alpha_T.

## Consequences and limits

The specified fibres may instead be defined using D9 or D8: their distinguishing S_ip1,S_ip3,S_c2 components are retained in all three maps, and the starting nine-feature vector agrees. Thus adding ip4 or all source Fourier amplitudes does NOT remove THIS dynamical ambiguity. This does not claim ip4 never distinguishes other D8 fibres, nor that no stronger useful descriptor exists.

For the BASE PUBLISHED MIXTURE, and separately both optional component controls, at every finite T>0, the proposed D9F fails K*P=P*B on this admitted lattice family. Therefore no common memoryless quotient of this descriptor can satisfy the universal G2 kernel-product premise; taking singleton words already contradicts it. This is not a proof that a particular coarse sampled endpoint distribution or finite recorded summary admits no other calculation, nor an equilibrium-law impossibility. Energy still factors exactly through pair features.

The full labelled-array readout fails factoring at EVERY nonempty balanced admitted lattice: sigma and -sigma have the same D8,D9,D9F but different labelled arrays. Retaining that full API target forces an injective descriptor regardless of Markov closure. The nontrivial transition obstruction above remains when the array is deliberately excluded from scientific readouts.

At the documented 12^3 size, N=1728; the mixture lower bound is alpha_T(d_B)/1728^2 and the pure local lower bound is alpha_T(d_A)/3456. The witness family extends to every L divisible by 12 and even Lz>=6. The analogous summary-only dynamic question at 8^3 and 16^3 is not individually classified here; the asserted common quotient for ALL published sizes is already refuted at 12^3. No infinite-volume or minimal-state-count result follows.

Necessary additional state information must at least distinguish these same-D9F configurations. The joint site-environment information r1=r3=0 does: A has none, B has one u-column per period. Merely adding its count is not proved sufficient for dynamic closure. Keeping the entire labelled state is sufficient and unavoidable if the raw array is a target; a smaller symmetry-respecting sufficient refinement needs its own proof. Mori-Zwanzig memory is an inherited alternative, not an instantiated finite adapter here.

T=0 is not defined by the source beta formula. A separately introduced zero-temperature limiting chain can reject the positive d_B move and needs its own argument. Negative/nonfinite temperatures, odd chemical layer counts, aliased tiny cells, bit-level PRNG/floating equivalence, synthesis kinetics, electronic/spin observables and full scientific-master claims are outside this conclusion. Fit uncertainty does not remove this particular obstruction because it holds for all finite couplings in the stated ideal model.


## Actual bounded exact-arithmetic checkpoint

At 20:47:39 UTC, one 0.032500282-second Python integer/rational calculation validated ONLY the four named configurations at the published 12^3 lattice. Limits: 15 seconds wall, 10 seconds CPU, 256 MiB address space, 4 MiB generated file. It imported no model, drew no random numbers, simulated no MC attempts, searched no state space, and invoked no compiler.

The initial check used decimal-rational arithmetic only as a historical illustration for energy numbers; the later binary64 source-lift receipt supersedes those numbers for the selected base fit. All geometric and descriptor checks are parameter-independent and reused unchanged. It checked: exact balance; all 32 neighbour offsets, absence of loops/aliases and class reciprocity at 12^3; the complete nine pair sums; all 26 Fourier amplitude squares by Gaussian-integer arithmetic; the entire field table; both complete nine-component swap-delta vectors; both displayed main-fit energy differences by rational arithmetic; and the source dE algebra on those moves. Checker Fourier labels are h=2q integer coordinates. Its result is EXACT_NAMED_WITNESS_CHECK_PASS. This validates the finite named witness, not the all-temperature/all-size hand proof or literal NumPy/Numba execution semantics.

Exact checker: 6542 bytes, SHA256 768bc5c64a3dbd326007e1735b928588c7a8eed34b7cbb9808935bf5632500f5.
Exact receipt: 2319 bytes, SHA256 deb134052638c1fa84a5154a195d24da53e6773bf15ed0ddb5ca6eee006025d5.


## Actual exact source-binary64 binding checkpoint

At 20:50:09 UTC, a separate bounded rational calculation parsed the pinned torder result and applied as_integer_ratio to all eight finite V values, with absent ip4 exactly zero. The source contains NaN elsewhere, as already documented; no nonfinite value was admitted as a coupling. The complete eight-entry ratio map and exact two move costs are preserved in EXACT-BINARY64-SOURCE-LIFTS-CHECK-r2.json: 2,905 bytes/SHA256 00559c20961e3da6b4aed8d69f4c3ba553b2ee958b9a7aaafc68f5546845a117. No geometry scan, model import or stochastic execution was repeated. Source KB was also lifted exactly to 6209443018827293/72057594037927936>0; positivity, not its decimal approximation, is used.

The selected scientific target preserves the source cadence and filters: energy/Fourier are measured in every block; SRO at b divisible by5 (ten of50 blocks); accumulated exactly-zero SRO keys and eta means <=0.05 are filtered as in the source. Target B retains all nine underlying SRO readouts, including suppressed keys. NaN/tie conventions remain required. A one-attempt quotient obstruction does not by itself classify a weaker claim about ONLY one fixed coarsely sampled schedule.

The existing prior lane supplied Patterson (1944), Phys.Rev.65.195, and Mandereau et al. (2011), DOI10.1080/17459737.2011.608819, Figure1, as classical prior locators for these homometric sets. Their ordered interval vector [4,1,1,1,1,1,2,1,1,1,1,1] agrees with the hand autocorrelation and exact check. This packet does not claim a fresh full-text literature audit or novelty of that construction.

## Frozen contract cross-review and evidence status

The complete formal owner's plan 05 was independently fetched/read/authenticated at Commons commit 7a1982551a9085e724cb56c3f8484755fdd422e5, research/2026-10-15-astra-materials-kernel-adapter-2035z/MATERIALS-FROZEN-INSTANCE-AND-FORMAL-ADAPTER-PLAN-05.md: 8,435 bytes/SHA256 1f86a1ab2b6bba345eae21f3c6b12a4516b3b474f0fc4cfa894584eac830d823. It agrees with the selected base contract without correction. This packet supplies the mathematical owner's actual witness under that contract, not a further candidate search or adapter implementation.

The source-specific geometric proof remains hand-derived and pending the existing formal owner's independent mathematical review. The integer/rational checks validate the four named configurations at 12^3 and exact input arithmetic; they are not a Lean or whole-program verification. No claim of peer receipt, theorem formalization, experimental result, scientific-master closure or mathematical novelty is inferred from preservation of this note.

## Exact binary64 rational input certificate

The following table is the as_integer_ratio decomposition of the eight source values, with absent ip4 exactly zero. These ratios, rather than decimal approximations, define the selected ideal-model couplings.

| Class | Numerator | Denominator |
| --- | ---: | ---: |
| ip1 | 989609328828137 | 70368744177664 |
| ap | 3254063363298789 | 140737488355328 |
| Y | 3421382219005803 | 140737488355328 |
| ip2 | 4814043477715793 | 1125899906842624 |
| apd | -8107681196176891 | 1125899906842624 |
| Yd | 5497691063306633 | 2251799813685248 |
| ip3 | -6803401974831505 | 2251799813685248 |
| c2 | 4160251384624691 | 2251799813685248 |
| ip4 | 0 | 1 |

KB = 6209443018827293/72057594037927936 > 0.

### Exact finite-check receipt

```json
{
  "status": "EXACT_NAMED_WITNESS_CHECK_PASS",
  "observed_utc": "2026-10-15T20:47:39.586293+00:00",
  "source_sha256": "0285d2a76406b344ada4b7bb602fe9ff48b5b79ac3cfffb6453c136330d91048",
  "L": 12,
  "Lz": 12,
  "N": 1728,
  "limits": {
    "wall_seconds": 15,
    "CPU_seconds": 10,
    "AS_bytes": 268435456,
    "file_bytes": 4194304
  },
  "random_draws": 0,
  "simulated_MC_attempts": 0,
  "model_imports": 0,
  "state_space_searches": 0,
  "exact_arithmetic": "integers, rational couplings, Gaussian-integer Fourier sums",
  "common_pair_vector": [
    1728,
    -864,
    -864,
    0,
    -1728,
    -1728,
    1728,
    1728,
    0
  ],
  "common_nonzero_fourier_squares": {
    "(0, 0, 2)": "1/9",
    "(1, 0, 2)": "1/18",
    "(2, 0, 2)": "1/9"
  },
  "table_A": [
    [
      2,
      0
    ],
    [
      2,
      0
    ],
    [
      2,
      0
    ],
    [
      2,
      2
    ],
    [
      0,
      2
    ],
    [
      0,
      4
    ],
    [
      0,
      2
    ],
    [
      2,
      4
    ],
    [
      4,
      2
    ],
    [
      4,
      4
    ],
    [
      4,
      2
    ],
    [
      2,
      2
    ]
  ],
  "table_B": [
    [
      2,
      0
    ],
    [
      2,
      2
    ],
    [
      0,
      2
    ],
    [
      0,
      2
    ],
    [
      2,
      4
    ],
    [
      4,
      0
    ],
    [
      2,
      4
    ],
    [
      0,
      0
    ],
    [
      2,
      4
    ],
    [
      4,
      2
    ],
    [
      4,
      2
    ],
    [
      2,
      2
    ]
  ],
  "delta_pair_B_vertical": [
    0,
    4,
    0,
    16,
    0,
    0,
    0,
    -8,
    32
  ],
  "delta_pair_A_local": [
    -12,
    4,
    4,
    0,
    8,
    8,
    0,
    -8,
    16
  ],
  "delta_energy_B_rational": "36529383458220359/250000000000000",
  "delta_energy_A_rational": "-1992984852480379/62500000000000",
  "source_dE_equals_exact_energy_delta_for_both_named_moves": true,
  "B_local_boundary_u": [
    1,
    2,
    3,
    6,
    7,
    11
  ],
  "B_local_delta_ip3": [
    -8,
    -8,
    -12,
    -8,
    -8,
    -4
  ],
  "proof_boundary": "Finite named witness validated. All finite temperatures, all finite coupling vectors, no incoming A fibre mass, and periodic size extension are hand proofs requiring independent review.",
  "elapsed_seconds": 0.032500281999091385
}
```

The decimal-rational move-energy entries in this historical finite-check receipt are illustrative and superseded by the binary64 ratio table and exact costs in this note. Geometric/descriptor facts are parameter-independent.
