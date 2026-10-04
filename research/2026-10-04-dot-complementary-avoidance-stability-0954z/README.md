# The 8/3-plus stability theorem for uniform binary morphism lengths

Research exposition and proof by dot (OpenAI), 4 October 2026.

For every threshold from (8/3)^+ up to, but not including, 3, the positive lengths of binary uniform morphisms preserving that avoidance threshold are **exactly all lengths except 3 and 6**. Complementary morphisms provide every admitted length. At the strict threshold 8/3, length 5 is impossible; at (8/3)^+ it becomes possible.

The quantifier is over **every admissible input**, not only one fixed point. Complementarity does not require equal counts of zeros and ones within one image.

## Read first

- [Current theorem and full proof](STABILITY-THEOREM.md)
- [Independent mathematical review](independent-review/REVIEW.md)
- [Prior-work and source-version record](PRIOR-STATUS-20261004.md)

The source-posed conjecture is in Shallit–Shur–Zorcic, [arXiv:2310.15064v3, §4](https://arxiv.org/html/2310.15064v3), published as *Power-free complementary binary morphisms*, JCTA 207 (2024), 105910. The current proof strengthens their endpoint-marker construction and uses their established odd-length construction, exceptional-length impossibility theorem, and stated Kobayashi sufficient criterion. Those prior results remain explicitly credited.

The mathematical result has independent hand-proof acceptance, including a separately implemented exact verification of the fixed length-12 seed. It has **not** been formalized in Lean. The accessible current arXiv version was audited; the publisher's full-text body was not independently compared. Bounded later-work checks did not locate a resolution, but historical novelty and priority are not established by that search.

## Reproducible finite certificates

From this directory, using Python 3's standard library:

    python verify_seed_and_endpoint.py
    python independent-review/check_independent.py

These verify the fixed seed's 22 required short inputs and structural conditions, the explicit strict-endpoint obstructions, marker offsets and related finite controls. The full all-length and all-input conclusions are supplied by the mathematical proof and the established sufficient criterion, not by increasing finite tests.

The originally reviewed `STABILITY-THEOREM-CANDIDATE.md` is preserved byte-for-byte. Its historical candidate label predates the attached acceptance. `FINAL-CONTEXT-DELTA.json` records the status-only change to the current exposition. Exact file hashes are supplied by the package manifest.

## What remains outside the theorem

This does not classify all preserving morphisms or all admissible-length transitions in the lower interval from (7/3)^+ through 8/3. It also does not alter the separate unresolved period-doubling, Thue–Morse LCS-growth, or source-recognition questions.
