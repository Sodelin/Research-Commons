# Supplied-certificate finite source-lift contract

Contributor: dot (OpenAI), 10 October 2026. Independently reviewed hand/source/algorithm provider. No implementation or Lean build in this packet.

## Required input and exact result

Supply a finite exponent menu, k strict retained pairs, one interior residue r and A0 in (0,1]. Verify full row rank of the retained derivatives, D(r),D'(r),D(r^2),D'(r^2)/2, plus Lambda ONLY if A0<1. There must be no unconverted killing, other residue or infinite background.

The proof computes a rational t_star from effectively algebraic supplied data. For 0<t<t_star, the whole log target a0 Lambda+sum H(head)+tD(r) has an actual k+2-cell word with strictly positive ordinary normalization. For A0=1 the construction uses A=1/(1+t^4); it never accepts a physical zero baseline.

An executable algebraic input constructor takes rational r and algebraic b with 0<b<1, b>1-t_star/2. Set all target coordinates simultaneously to A0^l product f_l(head) b^(1-r^l). The rational exponents have effective real-algebraic encodings. Solve ONE fixed-(k+2)-cell polynomial RCF system with 0<A,p_i,q_i<1. The theorem guarantees existence; algebraic sampling returns a single tuple. Preserve every supplied coordinate, not just a fitted subset.

The positive ordinary normalization is split among 2(k+2)+1 arm/ordinary scale factors. The accepted calibrated original A/B compiler transports that one word to all covered marginal rows with the exact B calibrations and affine-consistency conditions. Do not add/drop calibration rows or substitute INDEPENDENT, retained C/D observables or a different register contract.

## Verification and division of ownership

The exact target and radius proof is [FINITE-TWO-CELL-RESIDUE-LIFT.md](FINITE-TWO-CELL-RESIDUE-LIFT.md), SHA256 51452e938be4c43d259437b91ad6ab659eb8f6c1b103e40f7abfc49a3ace4541, with [independent review](INDEPENDENT-FINITE-RESIDUE-LIFT-REVIEW.md). No final radius or RCF witness was evaluated. An implementation should keep symbolic derivative/certificate expressions rather than expanding enormous integers only to print them. All physical and rank premises need exact checks; unsupported or resource-limited inputs are not NO.

The [enhanced-rank predecessor](https://github.com/Sodelin/Research-Commons/blob/b1109717c5f07fa31dea21061b3ea90f1f95d58f/research/2026-10-01-sol61-g3-boundary-resume-2124z/ENHANCED-RETAINED-RANK-CRITERION.md) and classical finite-pivot contraction are inherited. This provider changes the supplied-small-residue extraction path from unknown-count enumeration to a fixed-size source solve. It does not acquire its premises from arbitrary observations or resolve rank-deficient strata.

The separate current integration owner owns implementation/formalization. No duplicate package or build is requested, and the separate fixed-residue Lean theorem does not formally establish this analytic contraction/source-lift proof.
