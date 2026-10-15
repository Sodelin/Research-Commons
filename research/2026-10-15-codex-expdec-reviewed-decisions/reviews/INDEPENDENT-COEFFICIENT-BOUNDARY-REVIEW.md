# Independent review of the computable-coefficient boundary

Review date: 15 October 2026. Reviewer: `/root/independent_proof_review`, a separate Codex reasoning agent. Hand reasoning only; this is not external human peer review or formal verification.

Reviewed file: `research/COMPUTABLE-COEFFICIENT-BOUNDARY.md`.

- SHA-256: `bec5f45ef8035c9155ae9d3a7f06b36565b76478fc69e9524827d7026e794396`.
- Git blob: `d5c1af6079e34eb75ccba81d5e84394d993e9911`.
- Repository HEAD when inspected: `59909063745e842142e661d01c6a5d1c3b251352`.

## Verdict

Theorem 4 passes this scoped independent hand review. Its promise, uniform construction, total approximation program, error bound and reductions to exact equality, sign and constant functional identity are correct. No counterexample or substantive correction was found.

The undecidability arises from the coefficient representation. It already holds for deciding whether the supplied coefficient itself is zero. Exponential is an injective computable wrapper here; the result should not be presented as an unresolved transcendence phenomenon or as a negative result for explicitly encoded rational or algebraic constants.

## Representation and promise

The input is finite program text, together with the promise that every requested rational approximation terminates and has the specified error relative to one real value. The theorem does not require an algorithm for checking this promise. A proposed decider may behave arbitrarily on invalid programs; the reduction only feeds it valid programs.

The reduction remains valid even if a proposed decider inspects the program's source code rather than only querying its approximations. The transformation from the finite machine/input pair to that program text is effective, so such a decider would still give an ordinary algorithm for the underlying halting problem.

The range promise is particularly strong: every constructed value is either zero or a positive dyadic rational no larger than one half. Being promised a rational value is not the same as receiving its exact numerator and denominator. The denominator can be `2^t` for an arbitrarily late halting time, and no effective denominator bound is provided.

## Uniform construction and error audit

For each finite machine/input pair, generate a program with those finite data embedded. At precision input `n >= 1`, it performs a bounded simulation of at most `n` tested machine steps. This bounded simulation terminates regardless of whether the original machine ever halts. It then returns either zero or the exactly representable dyadic rational `2^(-t)`.

There are three cases:

1. If the original machine never halts, every returned approximation is zero and the represented value is exactly zero.
2. If it halts at a tested step `t <= n`, the program returns the exact represented value `2^(-t)`, so the error is zero.
3. If it halts later, `t > n`, the output zero has error `2^(-t) <= 2^(-(n+1)) < 2^(-n)`.

Thus the required non-strict approximation inequality is satisfied at every precision, including at `n = 1` and when `t = n`. The `t >= 1` convention gives the claimed maximum value `1/2`. A fixed wrapper can count inspection of an already-halting initial state as the first tested step; shifting a simulation convention by one would not change the reduction.

No oracle for nonhalting occurs in the approximation program. Nonhalting appears only in the mathematical description of its limit value. Likewise, no finite simulation is used to infer that a machine will never halt. These distinctions are what make the construction a valid computable name rather than an illicit halting oracle.

## Equality, sign and identity reductions

Strict monotonicity of real exponential and `exp(0) = 1` give exactly

\[
\exp(c_M)-1=0\iff c_M=0\iff M\text{ does not halt},
\]

and

\[
\exp(c_M)-1>0\iff c_M>0\iff M\text{ halts}.
\]

A total correct equality decider would answer the complementary halting question, whose Boolean answer can be inverted to decide halting. A total zero/positive classifier directly decides halting. Negative values never occur in this restricted family, so no ambiguity about the sign output is needed.

The classical contradiction can be expressed by the usual diagonal argument: given a purported total halting decider, construct a program that loops precisely when the decider says that program halts on its own description, and otherwise halts. Applying the decider to this self-input contradicts its prediction in either case. The coefficient construction would supply exactly such a prohibited decider.

Using `exp(c_M)-1` as a constant function on any fixed nonempty interval makes functional identity equivalent to its scalar zero test. The interval being nonempty prevents a vacuous identity on an empty domain. Neither variable dependence nor unbounded quantification is needed for this negative result.

For historical background only, [Turing's original paper, Section 8](https://theory.stanford.edu/~trevisan/cs172-07/turing36.pdf) establishes an undecidable machine-event problem. The present review uses the explicit modern halting diagonalization above and makes no historical novelty claim about the real-number reduction.

## Boundaries relative to the positive theorems

Every individual `c_M` has an exact rational encoding in the mathematical sense. There is nevertheless no uniform effective conversion from all the promised program inputs to such exact encodings: a converter followed by ordinary rational equality would decide whether `c_M` is zero and hence decide halting. The same obstruction applies to conversion to an effective algebraic encoding supporting exact zero comparison.

Theorem 1 receives those effective algebraic encodings as input. Theorem 2 uses a finite expression language with explicitly encoded algebraic constants. The current reduction does not construct such an expression uniformly from a machine; it constructs a coefficient program with potentially unbounded behavior hidden behind its approximation interface. It therefore proves no undecidability result for either finite algebraic-input expression language, regardless of the conditional status of Theorem 2.

No contradiction with the compact delta theorem arises. The nonzero values in this reduction can approach zero with no supplied positive separation. For any fixed positive tolerance, sufficiently late halting gives a positive residual small enough to receive the same relaxed answer as zero. For example, on `0 <= c <= 1/2`, the mean value theorem gives `0 <= exp(c)-1 <= 2c`, so those residuals can be made arbitrarily small by increasing `t`.

If an effective positive gap were additionally promised, such as `c = 0` or `c >= eta` for supplied rational `eta > 0`, numerical refinement would distinguish the cases. The reduction has no such gap. This is consistent with exact promised-margin decisions in the compact theorem, and confirms why its zero-margin boundary matters.

Finally, no reduction from the original finite algebraic-input biological G3 problem to this coefficient-program problem, or vice versa in the direction needed for a G3 undecidability claim, is supplied. Source coverage and arbitrary graph-size issues are separate. The draft correctly keeps them separate.

## Actual verification

Performed: exact source hash/blob inspection, independent reconstruction of every approximation-error case and decision reduction, and inspection of the cited primary historical background.

Not performed: running any machine, simulating any halting instance, SMT jobs, numerical experiments, compiler builds, installing tools, proof-assistant checks, source-language compilation or original G3 analysis. This review changes no theorem source, runtime, configuration, owner or hold. It is unstaged and uncommitted for root integration.
