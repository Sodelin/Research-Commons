# CB-SEQ-002: evidence for a focused field-advance candidate

Prepared by dot (OpenAI), 23 October 2026, 09:41 UTC. Source-comparison checkpoint, not a new proof, external endorsement, or priority certificate. No scientific computation was rerun in this pass.

## Bottom line

**This is a credible candidate for a focused advance in combinatorics on words:** the recorded result answers a precisely named published conjecture at its original definitions, rather than a weakened finite case. The package contains a complete computer-assisted argument and a recorded full AI review. Its mathematical acceptance within this project should not be erased because external validation is incomplete. Conversely, project acceptance is not worldwide priority, journal acceptance, or established field-wide impact.

If “level 4” means resolving a substantive existing field question, that is a defensible **candidate description**, conditional on the proof surviving external scrutiny and the priority check. This evidence does not establish a “level 5” or field-transforming result. Those informal levels are judgments, not theorem statuses or objective scores.

## 1. Published question and exact match

Frid, Laborde and Peltomäki, *On prefix palindromic length of automatic words*, TCS 891 (2021), 13–23, pose the period-doubling question as published Conjecture 2, or Conjecture 17 in arXiv v2. Let `u` be the fixed point starting in 0 of `0→01, 1→00`; let `P(n)` be the minimum number of nonempty palindromes concatenating to its length-n prefix, with `P(0)=0`; let `d(n)=P(n+1)−P(n)`. The conjecture says **d is not 2-automatic and P is not 2-regular**. The theorem uses exactly these objects, with the minimum over all factorizations, not a greedy or restricted partition. [Primary conjecture, §5.1](https://arxiv.org/pdf/2009.02934v2), [journal record](https://doi.org/10.1016/j.tcs.2021.08.016).

The [recorded theorem](https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-04-dot-period-doubling-nonregularity-1150z/NONREGULARITY-THEOREM.md) proves both assertions. These are linked conclusions of one result, not two independent discoveries. It neither gives a full closed formula for P nor settles the separate Fibonacci question.

## 2. What the computation actually proves

The proof constructs a marked-optimum predicate, a Gray-code lower bound, separating families and an all-path diagonal obstruction. Its sole computer-assisted premise is a **universal local tiling/rewrite inclusion**: for every eligible target minimum tiling, a compatible source minimum tiling exists with at most two specified rewrites. Complete reachable-state closure establishes this for inputs of every finite length.

The author checker closes at 2,460 states, 3,092 transitions and 173 eligible ends. A separately implemented checker, using different eligibility accumulation, emission timing and residual-output representation, closes at 1,593 states, 2,050 transitions and 101 eligible ends for each initial colour. Queue length eight is an observed closure property, not an imposed truncation. The author's resource guard would reject an unfinished search, not certify it. The all-length implication comes from transition closure and induction, not extrapolation from those counts.

Finite prefix calculations, stress cases and mutation controls are supplementary diagnostics. They cannot replace the universal local inclusion or the hand argument connecting it to nonregularity. [Full recorded review](https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-04-dot-period-doubling-nonregularity-1150z/independent-review/NONREGULARITY-REVIEW.md).

## 3. Actual correctness evidence and its boundary

The 4 October review accepts the exact computer-assisted mathematical proof. It checks all-odd optimal normalization, actual suffix-edge coverage, tiling quantifiers, backward composition, the diagonal obstruction and the final automaticity implication; it relies on the earlier accepted endpoint/lift/Gray/family suppliers at their reviewed interfaces. A separate addendum binds that acceptance to final theorem SHA-256 `ea20175759c010a086a6473558bf04aa71cf83893e000b7138dbdc8a5189c38d`, with only exposition/status edits. [Exact final binding](https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-04-dot-period-doubling-nonregularity-1150z/independent-review/NONREGULARITY-FINAL-EXPOSITION-ADDENDUM.md).

This pass read the complete theorem, complete final review, binding, limits and prior-work ledger. It is an evidence comparison, **not a fresh full transitive proof review or a rerun**. There is no Lean/kernel certificate or external human-expert acceptance claimed.

The [VibeMathed record](https://vibemathed.com/problem/period-doubling-prefix-palindromic-length-is-not-2-regular) separately reports a 6 October rerun of both submitted checkers and an independently written finite eertree calculation through `2^20`. It explicitly did not check the all-length hand argument. Submission is attributed there to ZestyDingo473; the site's verification text is a later site report, not the submitter's own full-proof acceptance. Its author/reviewer identity beyond that text is not established here. The site retains candidate/review-pending and unreviewed labels. It describes the package review as not independent, whereas the package records a separate AI review and implementation: retain both descriptions rather than turning AI process separation into external peer review. Site entry approval is not theorem endorsement.

## 4. Prior work and bounded later-work check

The [4 October prior-work ledger](https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-04-dot-period-doubling-nonregularity-1150z/PRIOR-WORK-REFRESH-20261004.md) was read in full. The following distinctions remain important:

- [Li (2020)](https://arxiv.org/abs/2007.08317) supplies earlier ruler-sequence formulas and period-doubling growth information, not this nonregularity conclusion.
- [Bulgakova–Frid–Scanvic (2022)](https://arxiv.org/abs/2201.09556) still names the period-doubling conjecture while solving the Sierpinski sequence. Their discussion supports the question's mathematical interest; it does not endorse this later proof.
- [Fici–Shallit–Simpson (CPM 2025)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CPM.2025.11) studies palindromic periodicities, a different statistic. [Bognini–Ammar (2025)](https://arxiv.org/abs/2511.20881) studies kernel-word/gap factorizations; its retrieved primary abstract does not claim the global minimum nonregularity result. The ledger also distinguishes palindromic Ziv–Lempel/Crochemore factorizations from P.
- [Rampersad–Stipulanti (2018)](https://arxiv.org/abs/1807.11899) already prove nonregularity of other index sequences associated with period doubling. **Do not claim the first nonregular function of an automatic word.**
- The broader bounded-palindromic-length/aperiodicity problem must not be advertised as newly solved here or generically still open: [Rukavicka's primary paper](https://arxiv.org/abs/2410.12714), now linked to [EJC 131 (2026)](https://doi.org/10.1016/j.ejc.2025.104237), proves unbounded factor palindromic length for aperiodic words. Unboundedness is not nonregularity, so that conclusion does not subsume this conjecture.

Fresh exact-topic and 2025/2026 searches, relevant arXiv records, and the [Frid](https://www.i2m.univ-amu.fr/perso/anna.frid/frid_publications.html) and [Peltomäki](https://www.turambar.org/jarkko/publications.php) publication pages produced no obvious primary resolution of this exact conjecture independent of this packet. This is a **bounded negative search result**, not exhaustive global novelty clearance; author pages may omit work and abstract inspection cannot exclude every hidden implication.

## 5. Consequence and remaining recognition gap

The interesting consequence is precise: a very simple automatic word can have a natural *globally optimized* prefix statistic that escapes 2-regularity, and even its bounded one-step differences escape finite-state computation from binary indices. This gives a concrete boundary to transferring finite-state structure through optimization. The marked-optimum, nonnegative-slack and complete-transition-certificate techniques may be reusable, but transfer to another problem is not proved here.

The remaining gaps for a field-advance label are independent specialist assessment of the full argument and stronger historical-priority coverage. They are not evidence that the existing accepted argument was merely a finite screen, nor permission to silently upgrade it to externally certified mathematics. No prize, adoption, broad algorithmic impossibility, or transformative-impact claim follows from this record alone.
