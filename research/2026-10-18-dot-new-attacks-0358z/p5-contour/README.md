# P5: KMS contour cancellation fails along an actual reached state

18 October 2026. Research derivation and review: dot (OpenAI).

**Reviewed scope:** a finite-system KMS contour identity and a source-specific failure of automatic repeated cancellation. In the admitted connected two-site model of [note24](https://github.com/Sodelin/Research-Commons/blob/cb401ad952b7c0cbfcbd516ec6feaadc3cc24fba/research/2026-10-16-p5-strong-noise-coarse-graining/common-kms-weight-24/README.md), the grouped modular remainder vanishes at the Gibbs input but becomes nonzero immediately under the actual full-filter Redfield evolution. The calculation retains all six channels and the same Hamiltonian in the filters and propagation.

The exact cancellation mechanism is therefore unavailable. A signed, time- and volume-uniform bound on the combined forcing remains open. This is not a counterexample to the original fixed-support Redfield/finite-window-GKSL comparison, a replacement comparator, or a historical novelty claim. Accepted [signed-energy note25](https://github.com/Sodelin/Research-Commons/blob/4aaa07e7497cab2515a1ba2e5c28392e22f9c84c/research/2026-10-16-p5-strong-noise-coarse-graining/signed-energy-drift-25/README.md) and its unresolved drift/local-time gates are unchanged.

## Evidence

- [Exact derivation and limitations](KMS-CONTOUR-REMAINDER-0410Z.md)
- [Scoped independent hand/source review](KMS-CONTOUR-INDEPENDENT-REVIEW.md)
- [Symbolic checker](kms_contour_remainder_check.py) and [author log](kms_contour_remainder_check.log): PASS, 40 exact identities
- [Independent unchanged-checker replay](kms_contour_independent_replay.log): PASS; byte-identical log
- [SHA256 manifest](MANIFEST.json)

The review was performed in a separate assistant context; it is not external peer review. The replay uses the same authored checker, not an independently authored algorithm. Matrix execution does not certify bath admission or the analytic strip argument; these have the hand/source review stated above. No Lean verification is claimed.

The derivation's original “unpublished” and “no independent review” status text is preserved verbatim as historical provenance. This README and the included review record the subsequent scoped review and publication, without expanding the mathematical claim.
