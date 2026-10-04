# Recovering the prior maximal-length bounds from the start classification

Prepared by dot (OpenAI), 4 October 2026. Addendum to the frozen three-family proof. The following are rederivations of established results, not novelty claims.

The all-start classification in Propositions 2 and 3 of `ALL-THREE-CANDIDATE.md` is proved without using the old upper bounds A(d). The old length theorems are only invoked afterward to identify the classified lengths as maximal. That dependence can be removed as follows.

For q=2^m, m≥2, a length-(q+3) monochromatic progression of difference q+1 would have both its first and second terms as starts of length-(q+2) progressions. Proposition 2 forces both start residues modulo q to be q−1. They differ by q+1, which is 1 modulo q, a contradiction. The l=3 construction gives length q+2. Thus A(q+1)=q+2.

For even m≥2, a length-(q+5) monochromatic progression of difference q−1 would likewise have two consecutive starts of length-(q+4) progressions. Proposition 3 forces both residues to be 1 modulo q, whereas their difference is −1 modulo q. Again this is impossible. The l=3 construction attains q+4, so A(q−1)=q+4.

For odd m≥3, take any start s=aq+b, 0≤b<q. Among the first q+1 terms of difference q−1, those with term numbers b and b+1 have indices

    (a+b)q,       (a+b)q+(q−1).

Their parities are opposite because t(q−1)=1. Hence A(q−1)≤q. The construction at q−1 attains q, giving equality.

These deductions make the three first-occurrence proofs self-contained in the elementary digit identities. Historical attribution still belongs to the previous length results: Parshina (WORDS 2015) and Aedo–Grimm–Nagai–Staynova (TCS 2022, Theorem 21 and Proposition 22), https://doi.org/10.1016/j.tcs.2022.08.013 .
