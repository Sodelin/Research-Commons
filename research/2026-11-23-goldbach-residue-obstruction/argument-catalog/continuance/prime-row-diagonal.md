# Prime-modulus rows: what factor swapping can and cannot cancel

Elementary regrouping of the actual side of the [corrected moving-cutoff comparison](https://zenodo.org/records/21939906), consistent with the Cloud cell decomposition. This does not handle the centered model or claim a new asymptotic estimate.

Let m=N−n. On the actual progression a row for modulus d has d|m and the cutoff m>αd. In the convention of the comparison, the nonzero actual cell weight is −Λ(N−m) μ(m/d) log(m/d); it is zero for nonsquarefree m. This follows from μ(d)μ(m)=μ(m/d) for squarefree m and the log difference log d−log m. Keep all original restrictions, including the chosen band and (d,N)=1.

For prime d dividing squarefree m, μ(m/d)=−μ(m). Grouping the prime-modulus actual rows by m therefore gives exactly Λ(N−m) μ(m) times the sum of log(m/d) over the eligible prime divisors d of m. Every eligible summand for the same m has the same sign, or vanishes. The strict moving cutoff is kept by filtering d<m/α, not by dropping it in the regrouping.

In particular if the cofactor is a squarefree semiprime, each eligible prime-modulus row has m with exactly three distinct prime factors and contributes nonpositively. Swapping a small factor of the cofactor with the modulus does not undo this: both terms, when eligible, have the same sign. For N=112 and m=105=3·5·7, Λ(N−m)=log 7, and the three possible rows have signs of −log 35, −log 21 and −log 15. At α<15 all meet the strict cutoff; a band restriction only removes terms. For a prime cofactor, in contrast, m has two distinct prime factors and the actual term is nonnegative.

**Consequence.** A pairing within one fixed complement m cannot supply actual-side sign cancellation between these classes in a prime-modulus band. Such cancellation must use different m or use the centered model. The model contains n throughout the cell, not just n=N−dk, so it has no implied term-by-term sign identity from this regrouping. This rules out one proposed shortcut, not a signed estimate across different complements and not the Goldbach strategy as a whole.

**Finite check.** For 2≤m≤10,000, compare the two sign formulas by trial division for each distinct prime divisor d of squarefree m: −μ(m/d)=μ(m). This checked 13,665 pairs (m,d). It checks the identity over a finite range; the multiplicativity argument above proves it in general.
