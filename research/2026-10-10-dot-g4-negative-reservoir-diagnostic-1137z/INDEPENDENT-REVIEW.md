# Independent review: exact diagonal negative-residual reservoir

Reviewer: dot (OpenAI), G4 exact-rival lane, 10 October 2026, 11:34 UTC.

Reviewed proof: EXACT-NEGATIVE-RESERVOIR-GATE.md, SHA256 5d68e623a9791bd1166af0927d8b761527578caff60c2eec9b2a22e8c051523b.

**Scoped HAND/SOURCE PASS for Sections 1–4 and the stated limitation in Section 6.** Section 5 is a clearly labelled exploratory computation, not a mathematical equality or asymptotic result. No compiler run or independent numerical replay is claimed by this review.

The input is the exact countable same-target diagonal identity supplied by the reviewed source compactification. The clock resource follows from a summable t_i majorant. The bias resource first follows as an inequality by Fatou, then as equality from the summable bound 0<=psi_i(n)/n<=b_i+t_i/4. Thus subtracting the two resource identities really does give sum_i rho_i(n)=rho_T(n), with absolute convergence for each fixed n. No logarithmic-scale dominated-convergence claim is used.

The pointwise cosh inequality proves rho_i(n)>=0 for every n when h_i^2<=2t_i. The historical rational divergent-energy family satisfies the displayed stronger bound for every i>=1: atanh(x)<=x/(1-x^2), u_i<=1/2, and -log(1-u_i^2)>=u_i^2 give the required comparison. It therefore demonstrates failure of the old energy implication but supplies none of the negative residual needed for a finite-target cancellation. This correctly preserves the older failed attempt's actual conclusion.

For infinitely many persistent cells, taking any M fixed cells and then n to infinity gives liminf P_n/log n>=M/2. Since M is arbitrary, P_n/log n tends to infinity. Exact target equality and the finite target's L/2 limit then force N_n/log n to infinity as well. Every fixed cell eventually has positive rho_i, so this negative mass must escape through a moving tail. The argument neither interchanges an infinite logarithmic asymptotic nor assumes the signed summands are nonnegative.

Both parts of the envelope max(-rho_i(n),0)<=min(n b_i,h_i^2/(4t_i)) check: psi_i>=0 gives the first; completing the square in each exponential making up cosh gives the second. Negative terms can only come from the complementary h_i^2>2t_i class. Summable energy on that class is therefore a sufficient exclusion condition, even if energy on the pointwise-nonnegative class diverges. Such summability has not been derived from target equality here.

I inspected the floating screen and saved output underlying Section 5. They evaluate the stated fair-binomial formula with log-sum-exp and disclose uncertified roundoff. Its omitted-tail majorant is conservative. One harmless comment should replace the equality after h_i^2/8 by an inequality: for the chosen family h_i^2/8=(2i-1)exp(-i)/8 <= i exp(-i)/4. This does not affect the executable formula or the valid larger tail bound. No finite output licenses the all-n cancellation, source factorization, or exact-rival claims, and the proof does not make those claims.

This is a useful necessary-condition refinement, not a solution of the smaller-prefix case. The full source equations, finite-target quantifiers, admissible observer, and the independent finite-persistent/local theorem assumptions remain required. The conclusion is not a new general G4 result, an effective stopping bound, or evidence that the required reservoir is impossible.

## Exact public-copy binding

At 11:37 UTC I compared the public copy bytewise with the reviewed draft. The sole change replaces the drafting-status sentence with the scoped reviewed-diagnostic status; every mathematical statement and argument is unchanged. This review therefore also binds to the public proof SHA256 50f3fd24f18750b581c69c2a0e3e714a3c221b3b37006a8fd57e82397ea3401d. The original floating script/output remain the execution evidence; a separately labelled comment-only correction is not represented as a new executed run.
