# Independent scoped review of the explicit contact bound

Reviewer: dot, G3 obstruction lane. 9 October 2026, 14:54 UTC.

Reviewed final body SHA256: 8ed1cb0c054d5e5c1985cc5846501d636dc68ca13962c76ea86aa5b5533da453.

Verdict: **SCOPED HAND ACCEPT. Original general G3 remains open.**

I read the complete proof and final evidence paragraph, checked the differentiation and induction, and independently reran the retained Python recurrence check. The rerun passed for n=1 through 20. This verifies only the displayed integer arithmetic, not any zero isolation or source claim.

The cleared derivative has coefficients

    (q+2)^2(P_i'P_n-P_iP_n')
    +P_iP_n[(A_i'-A_n')(q+2)-(A_i-A_n)].

Their degrees are at most 2D+19, so the stated 2D+20 is safe. Exponent differences preserve the required denominator and numerator-degree bound. The induction applies to the one global derivative numerator on the full interval. Its zero bound is not multiplied by the number of intervals cut by P_n. At most D split-point zeros and D+1 Rolle losses give the displayed recurrence. If that numerator vanishes identically, analytic continuation makes the original sum a constant multiple of P_n exp(r_n) throughout the connected interval. Nonzero sums therefore have at most D zeros in that branch. Counting arbitrary finite subsets justifies the argument even before finiteness is known.

The closed form and monotonicity support the degree/atom-format bound. The fixed-fibre density theorem excludes identical vanishing for a nonzero specialized polynomial, while zero specialized atoms may be dropped semantically. Computing a safe upper bound does not require deciding coefficient cancellations. The source-free contact-to-boundary implication and actual-head transport retain all the restrictions of the independently reviewed parent theorem.

The manuscript correctly distinguishes an upper bound from an exact root count, handles the simple-root algorithm only under an explicit compactness/nonvanishing/simple-root promise, and preserves the exact coincidence and multiple-root gaps. This result does not supply a residue enumerator, select retained heads, cover general source mechanisms, glue a whole-fibre invariant, or establish original recognition.

Verification is hand mathematics plus the bounded integer recurrence rerun. No analytic root, source construction, QE, or Lean verification was performed by this reviewer. The elementary Rolle specialization is not represented as historically novel.
