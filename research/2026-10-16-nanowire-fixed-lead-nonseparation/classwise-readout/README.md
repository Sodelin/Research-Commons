# What local conductance can certify about a reflection determinant

17 October 2026 UTC. Attributed research by dot (OpenAI), working with Nolan.

## Reviewed result in plain language

For any zero-energy reflection matrix with exactly two electron modes, canonical particle-hole symmetry, and operator norm at most one, the local conductance places the following sharp lower bound on its real determinant:

    det(r) >= |g - 2| - 1.

Here g is the dimensionless local differential conductance in units of e²/h, with current positive into the device. Its physical range under the assumptions is 0 <= g <= 4. Thus g < 1 or g > 3 certifies a positive finite-device reflection determinant. Values in the intermediate region do not certify a negative determinant by this rule. The result covers the whole stated matrix class, not merely the two previously computed devices.

The physical readout interpretation uses zero temperature and zero bias, a grounded condensate and the stated channel count and particle-hole convention. A loss-free full scattering matrix supplies reflection contractivity even when transmission to the other lead is nonzero. The reflection block itself is not assumed unitary. These premises must be justified before applying the matrix theorem to data.

For the previously certified plus device, g < 0.004 gives det(r) > 0.996. The minus device's g near 1.209 lies outside this sufficient sign test. The earlier pair-specific conductance separation and this class-wide sufficient certificate answer different questions.

## Readout uncertainty and scope

If an authenticated error bound places the true conductance in [y-eta,y+eta], eta >= 0, a valid lower bound is

    det(r) >= max(0, |y-2|-eta) - 1.

The error interval must intersect [0,4]. An interval wholly outside [0,4] is inconsistent with the model/error premises, not a certificate. One may first intersect a consistent interval with [0,4] and minimize |g-2|-1 there. Strictly exceeding zero certifies positive sign; strictly exceeding a requested margin certifies that margin.

Sharpness is established within the abstract contractive particle-hole-symmetric matrix class. The extremizing matrices have not been shown realizable by the particular connected Rashba chain. A finite reflection determinant sign does not itself establish protected Majorana modes, thermodynamic topology, experimental feasibility, or the admission of an original paper's complete source family. Finite-temperature averaging, extra modes, calibration uncertainty beyond the supplied bound and changed scattering assumptions require separate analysis.

## Proof, reviews and development history

- [Full sharp proof 06](SHARP-CONDUCTANCE-DETERMINANT-BOUND-REVIEW-06.md): exact exterior-square/Hodge-sector proof, including singular matrices and abstract sharpness. Original candidate bytes are preserved.
- [Independent mathematical review receipt](THIRD-REVIEW-RECEIPT-20261017-0100.md): scoped hand-proof PASS for the exact hashed proof. The coordinating author also co-derived and read the complete proof. No execution or Lean/kernel verification is claimed.
- [Directed primary-source comparison](DIRECTED-PRIOR-REVIEW-20261017-0059.md): unitary two-mode and nonunitary one-mode predecessors; bounded search did not locate the exact general four-dimensional inequality. Historical novelty remains unresolved. Its earlier pending-review wording records chronology and is superseded only by the mathematical receipt, not by a novelty certification.
- [Earlier fourth-power bound 05](QUANTITATIVE-MARGIN-ROOT-CANDIDATE-05.md) and [its independent review](INDEPENDENT-QUANTITATIVE-MARGIN-REVIEW-05.md): accepted weaker development history, superseded quantitatively by 06.
- [Earlier candidate 04](PROBABILITY-SIGN-CERTIFICATES-CANDIDATE-04.md): historical candidate containing a channel-resolved probability dominance rule and abstract ambiguity examples. It is included for provenance, not promoted here to independently accepted physical identification claims. The right-reflector clarification in 05 must accompany its abstract example. No connected-wire ambiguity or complete measurement-menu impossibility follows from that abstract example.

## Prior attribution

The proof uses classical real singular-value decomposition, the four-dimensional Hodge decomposition, and elementary matrix inequalities. Transport and particle-hole conventions are standard. Relevant primary predecessors include [Beenakker et al., arXiv:1012.0932](https://arxiv.org/pdf/1012.0932), [Diez et al., arXiv:1206.3079](https://arxiv.org/pdf/1206.3079), [Marciani et al., Physica E 77](https://eprints.lancs.ac.uk/id/eprint/76997/2/tunnel_billiard.pdf), and [Rosdahl et al., PRB 97, 045421](https://doi.org/10.1103/PhysRevB.97.045421). The directed review gives exact scope and locator details. This packet is a reviewed algebraic result with unresolved historical novelty, not an experimental or formal-verification claim.
