# A zero-bias conductance readout separates the certified finite nanowire pair

Author: dot, working with Nolan. Date: 2026-10-17 UTC.
Status: executed outward-rational candidate; independent review pending. No publication or experimental validation asserted.

## Result

For exactly the two rational devices of FINITE-PAIR-CERTIFICATE-02.md (SHA256 29662a1fdb14ef72b76b8d6daebcc76fde1af192c2e8ed38a3f50d722053f2b5), at B=2 meV and E=0, both the local and nonlocal ideal linear-response conductances distinguish the devices. Define dimensionless g=G/(e²/h), with terminal current positive from a normal lead into the wire. The superconductor and the unbiased normal lead are grounded. This is the usual fixed-condensate-potential transport interpretation of the packet's BdG scattering model; it is not a floating superconducting island with a charging constraint.

The exact outward-rational calculation establishes:

| Device | Local g_LL | Nonlocal g_RL |
|---|---:|---:|
| minus | (1209/1000,1210/1000) | (−791/1000,−790/1000) |
| plus | (3/1000,4/1000) | (−3/1000,−2/1000) |

Consequently g_LL(minus)−g_LL(plus)>1205/1000, and g_RL(plus)−g_RL(minus)>787/1000. Decimal presentations are approximately 1.2092764734 versus 0.0037593139 locally, and −0.7907089137 versus −0.0024580820 nonlocally. Only rational inequalities enter acceptance.

For a specified worst-case absolute readout radius ε_g, each individual channel separates this pair if its two possible reported-value intervals are disjoint. Thus ε_g<1205/2000 suffices locally and ε_g<787/2000 suffices nonlocally, in units e²/h. These are conservative sufficient radii from certified gap bounds, not the exact maximal radii or an instrument specification. Explicit simple thresholds are also certified: local errors ≤1/2 permit threshold 3/5 (above means minus); nonlocal errors ≤3/10 permit threshold −2/5 (below means minus).

This is compatible with the earlier energy-only overlapping-error-ball result. It shows that one additional ideal readout can distinguish these two examples, not that it classifies every opposite-label source.

## Channel convention and primary transport formula

The packet orders each site's four coordinates by spin first, particle/hole second. Hence τ_z=diag(1,−1,1,−1), electron indices are {0,2}, and hole indices {1,3}. A spin rotation or the conventional hole-spin relabeling within these sectors leaves the summed probabilities unchanged. Each normal lead has two electron and two hole propagating channels at E=0; spin is already counted and must not be multiplied by another factor two.

Rosdahl, Vuik, Kjaergaard and Akhmerov, *Andreev rectifier: A nonlocal conductance signature of topological phase transitions*, Physical Review B 97, 045421 (2018), Eqs. (3)–(5), define S_ij^{αβ} with incoming β in lead j and outgoing α in lead i, and T_ij^{αβ}=Tr[(S_ij^{αβ})†S_ij^{αβ}]. Their current is positive into the terminal from the device, opposite to our convention; negating their Eq. (4) gives

    g_ij = δ_ij N_i^e − T_ij^{ee} + T_ij^{he}.

Accordingly,

    g_LL = 2 − R_LL^{ee} + R_LL^{he},
    g_RL = T_RL^{he} − T_RL^{ee}.

This is zero-temperature, zero-bias differential charge conductance, not reflection determinant. An outgoing electron subtracts from current entering the wire, while an outgoing hole contributes with the opposite charge. The incident electron contribution is 2 in the local channel. The nonlocal channel contains no incident-current term. No extra Nambu-doubling factor is present.

Primary source: https://doi.org/10.1103/PhysRevB.97.045421
Accessible primary PDF, equations on article page 045421-2 (PDF page 3): https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf

## Exact leads and Green blocks

All original parameters remain unchanged: 60 sites, fixed t=501643/20000, λ=5/2, Δ=1/5, rational interior a_minus/a_plus, end onsite M=1000 meV, lead hopping and contact −τ_z meV, zero internal dissipation. The semi-infinite lead surface Green function is −iI at E=0, so its contact self-energy is exactly −iI. This follows channelwise from g=(E−g)^−1 with the retarded root at E=0; the ±1 hopping signs square out. The contact broadening is 2I. Thus the flux-normalized scattering convention of the original packet supplies

    K=−H+iΠ_L+iΠ_R, G=K^−1,
    r_LL=I−2iG_LL, s_RL=−2iG_RL.

Possible channel phases from the ±τ_z contact preserve electron/hole sectors and do not change the block Frobenius probabilities used here. No wide-band approximation at other energies is invoked.

## Extension of the verified Schur computation

Let U=−T and L=U^transpose be the upper and lower off-diagonal blocks of K. Write D_j for its onsite blocks, including +iI at the two ends. Backward elimination defines

    S_59=D_59,
    S_j=D_j−U S_(j+1)^−1 L.

All scalar and matrix pivots are certified nonzero by the inherited dyadic kernel. Therefore K is invertible and G_LL=S_0^−1. For the first block column G_jL, the eliminated homogeneous equations for j>0 give

    G_jL=−S_j^−1 L G_(j−1)L.

Iterating gives G_RL. This extension retains the same G_LL recurrence as the reviewed packet. The code additionally checks that every reconstructed block equation K G[:,L]=identity[:,L] encloses zero residual. These checks diagnose indexing/sign errors; invertibility and the algebra above are the mathematical justification.

For an entry z=x+iy, the probability uses the interval x.square()+y.square(), with exact integer outward rounding. Summing over the stated row/column sectors encloses each probability. The inherited kernel never uses floating-point acceptance.

A second check uses incoming-column unitarity. Since K−K†=2iΠ with Π=Π_L+Π_R, the resolvent identity implies G−G†=−2iG†ΠG (equivalently −2iGΠG†). For the contact scattering matrix S=I−2iW†GW, WW†=Π, this yields S†S=I. In particular r_LL†r_LL+s_RL†s_RL=I_4. The checker verifies all sixteen interval entries of this identity and the scalar consequence

    g_LL = 2 R_LL^{he}+T_RL^{ee}+T_RL^{he}.

These identities rely on the declared loss-free two-normal-lead model. They are not silently transferred to an absorbing or floating-island model.

## Reproduction and controls

Run in this new directory with existing Python 3, without −O:

    python test_interval_arithmetic.py
    python verify_conductance.py

The interval kernel, thirteen-control test file and its original helper dependencies are unchanged copies from finite-pair packet 02. The new verifier reconstructs both endpoint blocks, verifies block equations and incoming unitarity, then checks rational conductance ranges, gaps and threshold/error inequalities. The result file records source hashes and full exact endpoints. One initial control launch lacked the copied original helper module; its ModuleNotFoundError is retained in ARITHMETIC-CONTROLS-INCOMPLETE-PACKET.log. After supplying unchanged dependencies, all thirteen controls passed. No physical assumption is tested by those arithmetic controls.

## Scope and value

This provides a constructive readout for the two fixed examples in the ideal declared model. It does not establish robustness to parameter drift, finite temperature, dissipation, finite bias, model mismatch, fabrication tolerances, or a physically valid 1 eV barrier. The energy observation remains a closed-wire eigenvalue; the added conductance is an open-system response with the specified contacts. The distinction is explicit rather than treating the two experiments as interchangeable. Current polarity reversal changes both nonlocal signs but not separation.

The conductance formula and scattering methods are established prior work. The contribution claimed here is a checkable numerical certificate for this particular pair, pending independent review. Historical novelty is unresolved. Original Taylor implementation admission, physical Majorana protection and universal source-class identification remain unestablished.
