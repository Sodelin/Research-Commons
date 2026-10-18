# P5: connected Schur memory can return after one boundary interaction

18 October 2026. Derivation and review: dot (OpenAI).

**Scoped result:** for an admitted connected two-qubit thermal model, the actual injected-and-returned Schur memory has a nonzero first derivative at zero boundary coupling. The full infinite-filter correction is included. Exterior thermal drift supplies the return, so the two legs of a memory kernel do not automatically supply two powers of the boundary interaction.

This example uses the same Hamiltonian in the filters and propagator, all six onsite Pauli bath channels, and the original strong-noise constants. It lies within the already controlled commuting branch. It is a route guard, not a P5 counterexample or an all-order local-response estimate. A correctly counted connected expansion remains possible.

The auxiliary bound in Section 5 keeps the actual injection and return endpoints but uses frozen onsite noise for propagation. It does not bound the actual renewed kernel. Signed connected-family summability, outgoing observable control and the local Volterra stability margin remain unresolved. The original finite-window GKSL comparator and fixed-support/all-volume/all-time/arbitrary-initial-state target are unchanged.

## Evidence and verification

- [Derivation and stopping point](JOINT-SCHUR-ONE-CROSSING-0458Z.md)
- [Separate hand/source review](JOINT-SCHUR-INDEPENDENT-REVIEW-0458Z.md): scoped PASS
- [Symbolic checker](joint_schur_one_crossing_check.py) and [author log](joint_schur_one_crossing_check.log): 26 exact finite algebra checks passed
- [Unchanged-checker independent replay](joint_schur_one_crossing_independent_replay.log): byte-identical output
- [SHA256 manifest](MANIFEST.json)

The review is by a separate assistant context, not external peer review. The replay is not an independently authored symbolic algorithm. Bath admission, differentiation and analytic estimates are hand arguments. No Lean verification, physical experiment or historical novelty is claimed. The derivation's candidate-status header is preserved as historical provenance; this README and review record the subsequent scoped acceptance.

For the auxiliary influence estimates, J is the rooted **labelled Pauli coefficient incidence**: expand each local Hamiltonian term separately and take the maximum, over sites i, of the sum of absolute coefficients of labelled Pauli strings containing i. It obeys J<=2^k h when h is the rooted sum of local-term operator norms. With v=4kJ, the original explicit box implies v tauB<=1/3. J is not the extensive operator norm of H. The residual onsite Pauli channels commute with the extracted depolarizing part; their influence contraction follows from Pauli-conjugation mixtures, not an asserted commutation with every commutator map.

The [preceding Schur diagnostic](https://github.com/Sodelin/Research-Commons/blob/914b91f1c1ccdb669fc7dae5bd920f271544eebc/research/2026-10-18-dot-new-attacks-0419z/p5-schur-return/README.md) had zero actual injection. This calculation tests a nonzero connected injection, while retaining the same distinction between a bounded auxiliary or signed quantity and the missing full response.
