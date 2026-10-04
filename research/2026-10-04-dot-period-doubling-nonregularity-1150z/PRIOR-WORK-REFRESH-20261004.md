# Dated primary-source and later-work check

Prepared by dot (OpenAI), 4 October 2026. Checked again at 11:46 UTC before preparing any public submission. This is a bounded source audit, not a claim of worldwide priority or an exhaustive citation review.

## Exact source-posed question

Anna E. Frid, Enzo Laborde and Jarkko Peltomäki, *On prefix palindromic length of automatic words*, Theoretical Computer Science 891 (2021), 13–23, DOI https://doi.org/10.1016/j.tcs.2021.08.016 .

The current arXiv landing page https://arxiv.org/abs/2009.02934 records first submission on 7 September 2020 and latest revision v2 on 9 June 2021. The question is Conjecture 17 in that version and Conjecture 2 in the publisher's displayed body. It concerns the actual minimum number of nonempty palindromes partitioning each prefix of the fixed point a→ab,b→aa. Relabelling a=0,b=1 gives exactly the sequence used here. Its first difference is P(n+1)−P(n), with P(0)=0. The claim is non-2-automaticity of that difference and consequent non-2-regularity of P. It is not the distinct Fibonacci conjecture in the next subsection.

The original computational kernel growth is motivation, not a premise of the current proof. The regularity/bounded-difference automaticity equivalence is credited to the paper's Lemma 10 (published Lemma 2) and standard automatic-sequence closure results.

For catalogue dating, the publicly recorded conjectural question dates at least to the 2020 preprint; 2021 is the journal publication year.

## Earlier and subsequent work checked

- Frid's 2019 paper, https://cs.uwaterloo.ca/journals/JIS/VOL22/Frid/frid4.pdf , poses the broader formula/lower-growth and automatic-regularity questions (Problems 19–21). The present result does not supply a full closed formula for the period-doubling function.
- Shuo Li's 2020 preprint, https://arxiv.org/abs/2007.08317 , concerns the ruler and period-doubling palindromic-length sequences, including a period-doubling lower-growth result. Its current arXiv record still lists v1, 16 July 2020. It is credited as prior work; the current proof derives its own palindrome edges from the elementary floor recursion and does not require an imported edge-classification lemma.
- Bulgakova–Frid–Scanvic, *Prefix palindromic length of the Sierpinski word*, https://arxiv.org/abs/2201.09556 , current v3 of 14 March 2022, repeats the period-doubling nonregularity question while solving a different sequence.
- The current author publication pages https://www.i2m.univ-amu.fr/perso/anna.frid/frid_publications.html and https://www.turambar.org/jarkko/publications.php were read. The former includes 2026 work on small palindromic lengths in free groups; the latter includes publications through 2025. No solving sequel to the exact period-doubling question was identified on these pages.
- Fici–Shallit–Simpson, *On Palindromic Periodicities*, CPM 2025, https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CPM.2025.11 , and its arXiv record https://arxiv.org/abs/2407.10564 , study periodicities built from two palindrome blocks in several sequences. This is a different quantity from the minimum palindromic partition of every full prefix; no resolution of the target was identified in the checked record.
- The 2022 generalized period-doubling factorization work, https://ajc.maths.uq.edu.au/pdf/83/ajc_v83_p435.pdf , treats palindromic Ziv–Lempel/Crochemore factorizations. Those named factorizations are not interchangeable with the global minimum defining P.
- Earlier nonregular functions associated with period-doubling already exist, for example Rampersad–Stipulanti's *The Formal Inverse of the Period-Doubling Sequence*, https://arxiv.org/abs/1807.11899 . Its index-sequence nonregularity results concern different functions. No claim is made here to provide the first natural nonregular function of an automatic sequence.

## Search coverage and limit

The targeted searches combined the exact paper title, period-doubling, prefix palindromic length, nonautomatic/non-regular, conjecture, and 2025/2026. They were checked against the latest arXiv records, publisher question statement, and relevant author pages rather than relying on fixed-version URLs alone. The searches did not identify a later primary resolution to import. A missing hit cannot establish that no sequel exists, and the discovery may still duplicate unlocated or unpublished work.

## Verification terminology

Any accepted result from the accompanying packet should be described as an independently AI-reviewed, computer-assisted mathematical proof. The central local inclusion has two separately implemented all-length reachable-state checks. It is not a Lean proof, a human-expert endorsement, a journal acceptance, or a certified priority claim. These distinctions remain necessary even if the mathematical argument is accepted by its independent AI reviewer.
