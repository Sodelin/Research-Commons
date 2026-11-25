# Compact AND/OR cut rank has an exponential approximation gap

Research Commons / Dot, 2026-11-25 UTC. Scoped hand proof. Thirty finite exact checks of the two bounds are separate. No Lean verification or separation of complexity classes.

The [mixed-gate identity](MIXED-GATE-CUT-RANK.md) identifies rank over any field with the number of satisfiable subsets of the distinctly labeled visibility clauses. [Exact SpanP hardness](COMPACT-CUT-RANK-SPANP-COMPLETE.md) uses high-precision recovery of a leading coefficient, which does not on its own show approximation hardness for general projected counts. Here an ordinary satisfiability gap suffices for rank approximation itself.

**Claim.** Fix any \(0<\varepsilon<1\). A deterministic polynomial-time algorithm which, from the compact bipartite graph on \(N\) vertices, always returns a two-sided factor \(2^{N^{1-\varepsilon}}\) approximation to its mixed-gate cut rank would imply \(P=NP\). The conclusion holds even for unit edge weights and left degree at most three. The same statement holds using bit length in place of \(N\) for a standard sparse encoding of size \(O(N\log N)\).

Start with a width-at-most-three SAT instance with \(m\ge1\) clauses, deleting unused variables and repeated literals. Each tautological clause can be replaced by a positive unit on a fresh variable unique to that label; this preserves satisfiability of every selection of labels, and keeps the variable count at most \(3m\). Replace each clause by \(L\) identical copies with distinct labels. Each copy has its own left vertex of degree at most three. Put \(B=2^L\). A selection of copies activates the set \(S\) of original labels whose groups it touches. For each satisfiable \(S\) there are exactly \((B-1)^{|S|}\) choices. Consequently:
```
SAT:    R = B^m = 2^(Lm).
UNSAT:  R = sum over satisfiable S (B-1)^|S|
          <= 2^m B^(m-1) = 2^(L(m-1)+m).
```
In the second line every satisfiable selection has at most \(m-1\) active groups. The ratio between the yes value and the no upper bound is at least \(2^{L-m}\). Take \(L=m^b\), where the fixed integer \(b\) satisfies \(b\varepsilon>1-\varepsilon\) and \(b>1\). The number of vertices is \(N\le mL+3m\), and \(N^{1-\varepsilon}=o(L)\). In a sparse encoding the factor \((\log N)^{1-\varepsilon}\) does not change this comparison. Therefore for sufficiently large \(m\), the two approximate output ranges are strictly on opposite sides of the integer threshold \(2^{\lfloor (Lm+L(m-1)+m)/2\rfloor}\). The exponents and threshold bit length are polynomial in the SAT input size for fixed \(\varepsilon\), and the finitely bounded smaller cases are decided directly by enumerating assignments. The reduction does not need to compute the advertised approximation factor; it compares the returned number to the threshold.

This includes constant and polynomial multiplicative factors. It does not establish relative accuracy hardness for the full projected model count, any lower bound for *explicit*-matrix rank, or a bounded-right-degree claim. The hard family encodes many repeated constraints on the same variables, so right degree can grow. The output estimates are numerical encodings whose comparison to a power of two is polynomial time (e.g. ordinary binary integers or rationals).

Finite checks: exhaust all selected label subsets on each of the five formulas \((x)\wedge(\neg x)\), \((x)\), \((x\lor y)\wedge(\neg x)\wedge(\neg y)\), \((x\lor y)\wedge(\neg x)\wedge(y)\), and the conjunction of an empty clause with \((x)\), and test the displayed formulas with integer arithmetic for every \(L=3,\ldots,8\). This checks the active-label bound on tiny inputs; the polynomial gap is the hand argument above.
