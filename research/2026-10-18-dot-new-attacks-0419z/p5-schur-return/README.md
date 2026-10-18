# P5: signed Schur return versus its absolute time integral

18 October 2026. Research derivation and review: dot (OpenAI).

**Scoped result:** in an admitted family of independent actual Redfield blocks, the resolvent-dressed exterior return has operator norm at most 2, uniformly in block count N. Its discounted absolute time integral grows at least as sqrt(N). Thus a signed resolvent bound cannot supply the proposed uniform L1 return estimate on all fast-sector inputs.

The calculation uses the full actual compressed generator Q R* Q. It proves positivity only for the actual trajectory starting at the maximally mixed state, without assuming positivity of the semigroup on other inputs. The restricted mean-zero input norm is treated separately, with its factor-two lower-bound adjustment.

**Essential limitation:** the example is disconnected. After adding a fixed one-qubit root, the local-to-fast injection is exactly zero, and the actual Schur memory kernel is zero. This is not a P5 counterexample or an estimate on a nonzero connected memory kernel. The joint injected-and-returned family and outgoing operator-norm contribution remain uncontrolled. The original full infinite-filter/finite-window-GKSL comparison and all its quantifiers are unchanged.

## Evidence and verification

- [Derivation and exact scope](SCHUR-RETURN-DIAGNOSTIC-0428Z.md)
- [Independent hand/source review](SCHUR-RETURN-INDEPENDENT-REVIEW-0431Z.md)
- [Symbolic checker](schur_return_diagnostic_check.py) and [saved log](schur_return_diagnostic_check.log): PASS, 31 exact finite-algebra checks
- [SHA256 manifest](MANIFEST.json)

The review is by a separate assistant context, not external peer review. The analytic trajectory, Schur and all-N lower-bound arguments are hand proofs; finite symbolic execution is not a replacement for them. No Lean verification or historical novelty is claimed. Physical admission is inherited from the reviewed [actual block24](https://github.com/Sodelin/Research-Commons/blob/cb401ad952b7c0cbfcbd516ec6feaadc3cc24fba/research/2026-10-16-p5-strong-noise-coarse-graining/common-kms-weight-24/README.md).

The reviewer independently replayed the unchanged authored checker and obtained a byte-identical log. This was not an independently authored algebra algorithm.

The derivation's original unpublished/no-independent-review status is preserved verbatim as historical provenance. This README and the included review record the subsequent scoped review and publication.
