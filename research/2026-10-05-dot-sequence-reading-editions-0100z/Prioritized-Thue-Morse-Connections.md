# Prioritized connections worth pursuing

Prepared by dot (OpenAI), 4 October 2026. A focused mathematical map, not an exhaustive literature survey.

## 1. Block recognition → exact locations of extremal patterns

**Status: proved here and Lean-checked for the three specified Thue–Morse families.** Full blocks occur only in an aligned or half-aligned position. Local equal-letter constraints eliminate the half-aligned case and almost every start residue. The remaining starts are indexed by the simple three-letter condition t(l−1)=t(l+1)=1−t(l).

**Why useful:** this identifies every maximal start, rather than just guessing the first. For even m, the complete maximal-start set at difference 2^m−1 is the maximal-start set at difference 2^m+1 shifted by 2. It also turns a variable-product search problem into a short structural proof.

**Prior work:** the block-recognition method and progression lengths are in [Aedo et al. (2022)](https://doi.org/10.1016/j.tcs.2022.08.013); the exact first-location questions are [Joshi–Rust Conjecture 3.8 (2025)](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2). Worldwide novelty of the new all-start analysis is unassessed.

**Next missing bridge:** carry the location-sensitive argument through a different substitution, with its actual allowed block alignments proved anew. The existing ten-coordinate matching-height matrices do not supply that theorem automatically.

## 2. Non-coprime spacings → a companion automatic sequence

**Status: a concrete proof candidate, not independently reviewed or Lean-verified.** For u defined by 0→0011, 1→1100, the even-index subsequences lead to v defined by 0→0101, 1→1010. In fact u(2a)=u(2a+1)=v(a). This gives an exact way to study even spacings, which the naive “visit every residue” argument misses.

A proposed proof of the concrete p=q=2 case of Aedo et al.'s Conjecture 35 combines that reduction with an odd-prefix border obstruction. Reflection makes the border palindromic or antipalindromic; duplicated pairs in u force an odd palindromic prefix to be constant, while opposite pairs in v force it to alternate. The first few symbols prohibit the required long borders.

**Why useful:** this attacks the actual non-coprime obstruction stated in the source, instead of extending finite tables.

**Next missing bridge:** independent review of the full uniform argument and its scaling equalities, then formalization if accepted. The known special-difference maximum lengths should retain their original attribution. No claim is made for arbitrary p,q. [Primary conjecture and obstruction](https://oro.open.ac.uk/84734/15/1-s2.0-S0304397522004868-main.pdf), Conjecture 35 and the paragraph following it.

## 3. Exact digit recurrences → average, moments and distribution

**Status: the dyadic mean and arbitrary-cutoff sum algorithm are independently reviewed hand consequences of the inherited, proved ten-coordinate recurrence.** For k≥3, the sum of matching heights below 2^k is

    29(3k+1)2^k/72 − (k+3) − (7/9)(−1)^k.

The average therefore grows as (29/24)k. A fixed-size digit algorithm computes the sum below arbitrary N in O(log N) integer-matrix operations.

**Why useful:** the earlier sharp bound describes rare very large heights. The mean gives a different, aggregate description. Tensoring a linear digit representation provides a concrete route to exact second moments.

**Next missing bridge:** prove and audit the moment recurrence, then determine an appropriate normalization and whether a limiting distribution exists. A mean is not a typical-value or concentration theorem. These are project-specific questions, not claims that the general method is new.

**Prior work:** [Allouche–Shallit (1992)](https://doi.org/10.1016/0304-3975(92)90001-V) and [Heuberger–Krenn–Lechner (2024)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.AofA.2024.24). [Exact inherited recurrence source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/lean/SamuelAlexanderResearch/DigitRecurrence.lean).

## 4. Primitive juggling loops → renewal sums versus a prescribed prefix language

**Status: established coding and generating-function theory, with an independently reviewed application.** The primitive three-ball ground-state blocks (3) and (4,2) can be concatenated freely. Thue–Morse chooses a particular infinite order. Its prefix norm sum is rational when the two blocks have equal lengths; unequal lengths retain the classical Thue–Morse product and produce a natural boundary.

**Why useful:** this explains exactly why a rational unrestricted counting theorem need not survive restriction to one automatic prefix language. The prefix set is not closed under concatenation, so an unrestricted renewal identity cannot simply be reused.

**Next missing bridge:** identify a genuinely interesting family of constrained juggling languages whose enumeration transfers more than this classical coding example. A new throwing-height bound does not follow: physical throws stay at most 4, and the transferred bound concerns matched beat count in an additional constraint graph.

**Prior work:** [Chung–Graham (2008)](https://fanchung.ucsd.edu/wp/pjs.pdf), [Elsner–Klyve–Tou (2012)](https://digitalcommons.tacoma.uw.edu/ias_pub/850/), and [Tou's asymptotic continuation (2019)](https://doi.org/10.1142/S1793042119500568). Natural-boundary theory is classical; see [Allouche (2015), §3.8](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.906.pdf).

## 5. Limits of the same toolbox: subsequences and palindromic length

**Status: separately posed questions, still unresolved in the checked sources; no proof supplied here.**

- An exact formula for the longest common subsequence of complementary Thue–Morse blocks requires controlling arbitrary deletions. The missing bridge is a finite, exact description of dynamic-programming boundary data. Our arithmetic-progression recognition and matching-height recurrence do not encode those deletions. [Blikstad (2020)](https://arxiv.org/abs/1904.00248) proves asymptotic results, not the requested exact formula.
- Period-doubling prefix palindromic length is conjectured not to be 2-regular. The missing bridge is an infinite family of distinguishable kernel elements or another genuine nonregularity argument. Bigger finite state/rank calculations cannot settle it. [Frid–Laborde–Peltomäki (2021), Conjecture 17](https://arxiv.org/pdf/2009.02934).

**Why useful:** these mark where the successful finite-state method must change, rather than encouraging a false claim that every automatic-sequence statistic has a small recurrence.

## Recommended order

First complete the public, source-linked handoff of the fully checked first-occurrence theorem. Next review the companion-sequence/border candidate in item 2. The strongest independent extension with direct leverage is the matching-height second-moment problem in item 3. Keep the juggling application precise and credited; take the LCS and nonregularity problems as later projects requiring genuinely different proof ingredients.

The follow-up search was bounded. “Unresolved in the checked sources” does not certify that no later or unpublished solution exists.
