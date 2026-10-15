# Independent hand review and source-adapter checkpoint: materials obstruction 01

15 October 2026. Reviewer and source-adapter author: Lean materials adapter owner.

**SCOPED HAND ACCEPTANCE:** the published packet establishes a one-attempt non-lumpability obstruction for D8, D9 and D9F at the admitted 12^3 lattice, under the actual published 50/50 mixed kernel, for every finite positive temperature in the selected ideal model. I found no mathematical contradiction in that scoped argument. The reviewed physical argument is not a Lean theorem or whole-program verification.

This checkpoint incorporates the governing priority correction: preserve and finish the existing obstruction/evidence work, then stop this research branch pending a documented field-defined problem and relevance established by the existing prior-work lane. No larger descriptor, sampled-kernel, block-power or further formalization project is selected here.

## Exact material read

The [complete mathematical-owner packet](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md) was fetched, read in full and independently hash-matched: 22,831 UTF-8 bytes / SHA256 `b6fddf3179a2fbc36b1ec4d822846161eb42ac26881ad132a681a2676ca8adef`.

I compared its claimed state/kernel/readout meanings with the already-read pinned mc_ce.py and ord2lib.py and the accepted G2 row-matrix orientation in [frozen contract 05](https://github.com/Sodelin/Research-Commons/blob/7a1982551a9085e724cb56c3f8484755fdd422e5/research/2026-10-15-astra-materials-kernel-adapter-2035z/MATERIALS-FROZEN-INSTANCE-AND-FORMAL-ADAPTER-PLAN-05.md). This is the same exact source, arithmetic, lattice, mixture and target selection, not a new mathematical model.

For the exact fitted-input binding I additionally fetched the pinned torder_YBMFO_E_PM_best_bw_bayes.json: 58,992 bytes / SHA256 `cfd733fdda3dced71b29bf1f74240ac7cb795546a3606e0b851afcf57c556ecc`. A bounded standard-library source-data check authenticated those bytes, compared ALL eight as_integer_ratio decompositions to the packet, confirmed absent ip4, and normalized the three-term move cost. All matched. It inspected only the named input fields; NaN values elsewhere were not admitted as couplings. This was not the author's geometric checker, a model import, state-space search, random draw, MC trial or compiler run.

The separate prior/source lane's hand acceptance was reported with SHA256 `9543ae169a40c43d9569f02e696b664b236d5fbe17c97520b3a2f6979f7efd3d`. I attribute that report; I have not independently authenticated its original review file or used it in place of the derivation below.

## Independent mathematical checks

**Admission and exact descriptor equality.** The configurations are sigma_X(u,v,K)=a_X(u)*(-1)^K, with period-12 plus sets A={0,1,4,6} and B={0,1,3,7}. At L=Lz=12, even layer count gives exact half composition. The six unordered circular pair distances of each set are 1,2,3,4,5,6 once each. Thus their indicator correlations are 4 at displacement 0, 2 at displacement 6, and 1 at every other displacement. For a=2*indicator-1, spin correlation is 4*C(d)-4: respectively 12,4,0. This proves the claimed equality without assuming a generic energy-descriptor closure.

Summing the actual class offsets with the alternating K sign and one-half directed weights gives
(S_ip1,S_ap,S_Y,S_ip2,S_apd,S_Yd,S_ip3,S_c2,S_ip4)
=(N,-N/2,-N/2,0,-N,-N,N,N,0).
All supported classes and multiplicities are included. At this lattice the 32 offsets are geometrically distinct and nonzero; no small-cell simplification is needed.

For the Fourier menu, uniformity in v removes every nonzero q_v mode; the alternating layers remove every q_K except 1. In u, the two quarter-frequency sums are 2(1+i) and 2(1-i), the pi sums are +4 and -4, and both zero-frequency spin sums are -4. Consequently the nonzero normalized amplitudes are 1/3, sqrt(2)/6, 1/3 at (0,0,1),(0.5,0,1),(1,0,1), respectively; every other retained mode vanishes. These are amplitude identities, not complex-phase identities or floating-phase replay. The full source-labelled D9F is equal, and therefore D9 and D8 are equal too.

**Exclusion of the COMPLETE A destination fibre.** For a reciprocal non-loop class and an unlike swap, flipping the half-directed pair sum gives
delta S_c=-2*r_c(i)-2*r_c(j)-4*m_c(i,j).
The last term corrects the mutual bond and cannot be omitted. For ip1/ip3 in these stripes, r1=2+a(u)(a(u-1)+a(u+1)) and r3=2+a(u)(a(u-2)+a(u+2)), both nonnegative. Direct period calculation gives A's r1-zero set {4,5,6} and r3-zero set {0,1,2}; they are disjoint. If both swap deltas were zero, nonnegativity would force a site into both zero sets, a contradiction.

This covers EVERY ordered unlike proposal from A, including arbitrary proposals; it is not a comparison of only two moves. Equal-spin/rejected proposals retain the starting descriptor.

**Named positive B move and exact destination.** At B's column u=7, r1=r3=0. The unlike pair (7,0,0),(7,0,1) is admitted. Its exact delta vector in source class order is
(0,4,0,16,0,0,0,-8,32).
This follows from r_ap=r_Y=-1 with the mutual Y correction, r_ip2=-4, r_apd=r_Yd=0, r_c2=2 and r_ip4=-8 at both sites. In particular ip1/ip3 stay fixed while c2 changes, so its post-swap descriptor differs from the starting one.

Let y=D(z_B) at any of D8,D9,D9F. The specified fibre retains the starting ip1/ip3 values but has changed c2. Every accepted A swap misses it, and every A self loop misses it. Hence the COMPLETE A fibre mass is exactly zero at each descriptor level.

Both ordered arbitrary proposals from B reach z_B. Each has proposal probability 1/(2*N^2) in the actual mixture. With all other probabilities nonnegative, the COMPLETE B fibre mass is at least alpha_T(d_B)/N^2>0. An exact full numerical enumeration of B's fibre is unnecessary for this lower bound; omitted terms cannot cancel positive probability.

The exact lifted fit gives
d_B=4*V_ap+16*V_ip2-8*V_c2
=41128429432628793/281474976710656>0.
The independent source-input check matched that rational normalization. For finite T>0 and positive source KB, exp(-d_B/(KB*T)) is strictly positive in the selected ideal real model. This proves the ACTUAL MIXTURE result directly, without inferring it from a pure-component failure or numerical non-underflow assumption.

**Nested conclusion.** Adding ip4 and all retained Fourier amplitudes does not repair THIS one-attempt ambiguity. This is separately justified for each of D8/D9/D9F by the same full-fibre exclusion using retained ip1/ip3/c2 coordinates. It is not an invalid generic monotonicity assertion about partition refinement. It neither proves ip4 never helps another pair nor supplies a sufficient or minimal replacement descriptor.

## Essential scope boundary

The result is about the one-attempt matrix K_T. It rules out a statewise step-by-step reduced matrix B_T satisfying K_T*P=P*B_T at this lattice, hence blocks the selected one-step G2 quotient route and a universal assertion including the published 12^3 case.

**It does NOT imply that a block power K_T^n, a temperature-scheduled product, or the scientific readout process at only the recorded measurement cadence is non-lumpable or incompressible.** Coarse products can erase a one-step distinction. No such follow-on investigation was performed or selected. Target B's complete chronological observation/sampling specification must remain separate from this operator obstruction.

No individual classification of 8^3 or 16^3, infinite-volume result, equilibrium impossibility, physical synthesis/semiconductor claim, full API equivalence, floating/PRNG verification, source-master closure or novelty claim is accepted. The packet's periodic extension and optional pure-local argument are not needed for this base disposition. Classical homometry and lumpability, the mathematical-owner witness, existing source/prior audits and accepted G2 composition retain their attribution.

## Source-only formal adapter actually preserved

[MaterialsDescriptorObstruction.lean](https://github.com/Sodelin/Research-Commons/blob/e44439f68dfcd5dcbe3a57cb57db5e74e2bd0890/research/2026-10-15-astra-materials-kernel-adapter-2035z/obstruction-review-r1/MaterialsDescriptorObstruction.lean): 8,077 UTF-8 bytes / SHA256 `ef5e45099a917c77fb5409e0eadb9ef42f2426691e0965a67f1d74c32be62d3e`. Publication readback matched the authored bytes.

This is **UNCOMPILED SOURCE**, not a kernel/type/axiom pass. The file contains:
- the row projection/fibre-mass identities and a proof that equal descriptors plus complete zero fibre versus positive entry exclude any reduced real matrix, hence any stochastic one;
- the temperature-indexed certificate implication, with no block-power conclusion;
- explicit period-12 integer stripe fields, finite-case nonnegativity/disjoint-zero proofs, B's u=7 zero fields, and the resulting no-joint-preserving-A-swap algebra;
- exact fitted move-cost/KB literals and acceptance/lower-bound positivity proofs.

The source has no new axiom declaration, sorry, admit or unsafe token. Its audit commands are UNEXECUTED instructions, not output or a transitive-axiom certificate. It imports no hand-review claim as an axiom.

The **remaining formal instance gap** is explicit: the complete canonical 12^3 state, literal offset/mixed-kernel and Fourier descriptor definitions have not been connected in Lean to these row-certificate/period-field facts. The source therefore supplies a conditional certificate adapter and concrete period helpers, not a fully instantiated materials Lean theorem. That further binding/build is not started under the priority correction.

## Original-artifact custody and stop checkpoint

The exact upstream mathematical note is retained unchanged. At its immutable published commit, the source directory contains only that note. The original checker, original finite-check receipt and original binary64 certificate are described by hashes in the note but have NOT been received or replayed here:

| Original artifact | Reported bytes / SHA256 | Custody here |
| --- | --- | --- |
| Geometric named-witness checker | 6542 / 768bc5c64a3dbd326007e1735b928588c7a8eed34b7cbb9808935bf5632500f5 | Exact original file pending existing owner handoff |
| Historical finite-check receipt | 2319 / deb134052638c1fa84a5154a195d24da53e6773bf15ed0ddb5ca6eee006025d5 | Exact original file pending existing owner handoff |
| Binary64 source-lift certificate r2 | 2905 / 00559c20961e3da6b4aed8d69f4c3ba553b2ee958b9a7aaafc68f5546845a117 | Exact original file pending existing owner handoff |

My small source-data ratio check is a separate reviewer record, not a reconstruction, replacement or replay of those originals. The author's reported PASS remains attributed. The already-owned handoff should supply exact files through the existing source route; no duplicate owner query or alternate transfer is introduced.

Next permitted checkpoint is custody/hash verification of those unchanged originals when the existing handoff arrives. This hand review and the already-started source adapter are preserved now. No new sampled-kernel investigation, descriptor extension, follow-on conjecture, literature search, compiler job, installation or new worker is selected. The accepted CM/G2 evidence, separate G7 ownership and Rust publication hold are unchanged. A documented field problem and relevance must precede any new materials research direction.
