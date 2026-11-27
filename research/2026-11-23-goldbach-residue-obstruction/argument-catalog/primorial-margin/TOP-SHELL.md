# Discarding the top modulus shell at the sharper error scale

Research Commons hand audit of the Codex Pointwise Sieve follow-up. No Lean verification. This is an absolute bound on a localized part of an exact signed error, not cancellation in the remaining sum.

Let L=log N, α=√N/L^K for fixed K, Q=N/α, and I=((1−δ)Q,Q). The corrected long error sums over (q,N)=1 in I and n<N−αq the terms

    μ(q)Λ(n)μ(N−n) log(q/(N−n)) [1_(q|N−n) − 1/φ(q)].

This keeps the strict endpoint in [Moya's correction](https://zenodo.org/records/21939906). All n in the shell satisfy n<δN. For 0<δ≤1/2, using q/φ(q)≤ζ(2)Σ_{d|q}1/d and counting multiples of d in I gives

    Σ_{q∈I} 1/φ(q) ≪ δ + log(Q)/Q.

The model is at most O(δNL(δ+L/Q)) in absolute value, by Chebyshev on ΣΛ(n), since the log weight on this support is at most L in magnitude. For the actual prime part and δ≥L⁻², log(δN/q)≍L. The [Brun–Titchmarsh bound as recorded by Maynard, (1.3)](https://arxiv.org/pdf/1201.1777) with the reduced residue N modulo q then bounds weighted prime mass by O(δN/φ(q)). Summing with the remaining log weight gives the same bound as for the model. Actual proper prime powers cost O_ε(N^(1/2+ε)L³) for fixed ε∈(0,1/2), by the divisor bound for N−n. The model already included prime powers. For smaller δ, dominate both absolute sums by those with δ=L⁻²; enlarging the shell does not change any summand already included.

Thus the shell is o(N/L) whenever δ=o(1/L), for example δ=1/(L log L), uniformly in the individual target. At δ=c/L the same argument gives O(c²N/L)+o(N/L): choosing a sufficiently small fixed c would spend only a fixed fraction of the [uniform margin](README.md), but it does not give little-o for fixed c. No claim of necessity at this boundary. The remaining bulk and the exact pointwise twisted estimate are open. The Codex audit also reported 120 finite exact-cutoff support fixtures; this hand bound does not depend on them.
