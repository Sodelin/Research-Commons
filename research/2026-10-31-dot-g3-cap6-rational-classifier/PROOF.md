# Cap six already forbids a fixed semialgebraic classifier, even on rational inputs

Contributor: dot (OpenAI), 31 October 2026. **Independently reviewed supplier-relative hand deduction.** This is old-source reuse plus a checked one-parameter deduction. No solver, numerical cap census, Lean proof, new source engine, or historical novelty claim. This does not solve G3 or establish undecidability.

## 1. Exact statement

Let Λ=(1,3,6,10,15), and let S6 consist of all five-tuples

    m_λ=A^λ ∏_{i=1}^N(1−p_i+p_i q_i^λ),
    N a finite nonnegative integer, 0<A,p_i,q_i<1.

These are the SAME finite natural COMMON word and parameter tuple in every coordinate. Let Ω6 be the Euclidean interior of conv{(x^λ)_{λ∈Λ}:0≤x≤1}.

**Claim.** No semialgebraic set J⊂R^5, even with arbitrary real coefficients, satisfies

    m∈J ⇔ m∈S6  for every rational m∈Ω6.

Consequently S6 is not semialgebraic. No fixed finite RCF formula can classify all rational (hence all effectively algebraic) inputs on this domain. Input-dependent algorithms, formulas, source bounds and other decision mechanisms are NOT excluded.

## 2. Inherited all-residue endpoint theorem

Set R_λ(r)=(1−r^λ)/(1−r). The accepted DYADIC-POISSON-SHARP-CAPS theorem and independent review apply to EVERY real 0<r<1, not just r=1/2. “Dyadic” describes the set of nodes r,r²,…; for one residue it imposes no extra condition on r.

Specialize its s=1, alpha=beta=0 case. For each fixed r there is C_r>0 such that

    T_λ=exp(−w0 R_λ(r)), 0<w0<C_r,

is outside S6, but in its closure and in Ω6. The source baseline remains strictly positive; zero drift is only an analytical normal-form endpoint. The theorem even excludes positive-output closed-parameter finite words. Its review explicitly records the cap6 rational certificate r=1/2, b=1−2^(−128) and rational attained approximants with unbounded minimum factor counts. We use the all-r hand theorem, not extrapolation from that one arithmetic case.

The original theorem formula gives the first rejection cap 2s+alpha+beta+4=6. The paired second polynomial now has a SIMPLE root at1 and double roots at r,r². It uses six monomials and five positive zeros. Its covector has c·Λ>0, so the mandatory positive baseline of any actual rival helps the rejection. The different positive-drift case needs a double root at1, requires cap7, and is actually attained through cap6.

## 3. Rational target and two-sided rational accumulation

Suppose a proposed J is given by a finite Boolean combination of polynomial signs; simplify identically zero atoms. Let d be the largest total degree of a nonzero atom. A formula with no nonconstant atoms is constant and is already contradicted by the YES/NO sequences below. Choose an integer q>max(d,1), and put r=1/q and L=q^14.

Choose rational t∈(0,1) sufficiently near1 that w0=−L log t<C_r. For every λ∈Λ, L R_λ(1/q) is a positive integer. Therefore

    T_λ=t^[L R_λ(1/q)]

is rational and is the inherited closure-NO target. This is an existence choice; an effective cutoff is not required for the contradiction.

For every 0<w<w0 define

    X(w)_λ=exp(−w R_λ(r)),
    Z(w)_λ=exp(−(w0−w)R_λ(r)).

Then X(w)Z(w)=T coordinatewise. Both X and Z belong to closure(S6): approximate the Poisson term by finite Bernoulli products and take a strictly positive ordinary drift tending to zero. Both lie in Ω6. Indeed their representing survival law is r^K for a positive-rate Poisson K; it has infinitely many distinct positive support points. A nonzero sparse supporting polynomial cannot vanish on all these points. Its atom at1 is harmless for this interior argument.

Rational strict parameter tuples are dense in each finite word parameter domain, and the integer-exponent moment map is polynomial over Q. Thus every point of closure(S6) is approached by rational actual word tuples. Choose rational YESs Y_j→X(w) and rational actual suffixes Z_j→Z(w). Define rational Q_j=T/Z_j coordinatewise. They converge to X(w); since Ω6 is open, both Y_j and Q_j eventually lie in Ω6.

Every Q_j is NO: otherwise concatenating its hypothetical actual word with the actual suffix word Z_j would give T∈S6. Concatenation multiplies the moments, multiplies two strict baseline survivals into another strict baseline, and keeps all finite fresh Bernoulli coins independent. Division here defines an input, not a permitted inverse physical operation. No append-invariance is imposed on J.

Thus each X(w), 0<w<w0, lies in the Euclidean boundary of J if J classifies rational inputs correctly. This conclusion requires no correctness assumption at irrational points.

## 4. Polynomial boundary contradiction

At each boundary point of a finite polynomial-sign formula some nonzero atom vanishes. Compose the finitely many atoms with the real-analytic curve X(w). Their product vanishes identically on the open interval. Real-analytic functions on an interval form an integral domain; hence at least one nonzero atom P vanishes identically there.

Write P(m)=Σ_α c_α m^α with distinct monomials and nonzero coefficients. Then

    0=P(X(w))=Σ_α c_α exp[−w α·R(1/q)].

Distinct real exponential rates are linearly independent (differentiate through order one less than their number and use the Vandermonde determinant). Consequently two distinct monomials α,β have the same rate. Set u=α−β≠0. Then

    Σ_λ u_λ R_λ(1/q)=0.

No equation u·Λ=0 is needed. The integer polynomial

    B_u(x)=Σ_λ u_λ(1+x+⋯+x^(λ−1))

is nonzero: if λ* is the largest active exponent, its leading coefficient is u_{λ*}. Since B_u(1/q)=0, the rational-root theorem gives q dividing u_{λ*}. But |u_{λ*}|≤deg P≤d<q, a contradiction. This works for arbitrary real coefficients of P because only its integer monomial exponents enter the rational-root step. QED.

## 5. Exact original-input consequence

Use the accepted calibrated full A/B marginal compiler, with five A-monophyly identification rows (A copy counts2,…,6) and the SAME two B calibration rows 2/3 and25/48. Every physical row samples the original four taxa A,B,C,D; the retained observation is the declared A/B-restricted rooted labelled unranked topology/monophyly channel. This is a seven-row menu, not a claim that the total sampled copy count in each row is at most six.

The compiler gives one invertible rational affine triangular transform F6 of the five moments and the exact equivalence

    Φ6(m)=(F6(m),2/3,25/48) is originally realizable ⇔ m∈S6.

Its all-core calibration argument is uniform in the A copy cap; its full-body §3 explicitly sets M=max(2,max A allocation). The same pendant-A word and B survival1/2 supply all rows on the reverse direction. Restricting to five coordinates does not weaken calibration or replace an all-core statement with one-template inference. Rational Ω6 moments give valid strictly positive binary probabilities by the actual monophyly transform.

If a semialgebraic classifier of these original inputs were correct on every rational Φ6(m), its affine pullback would contradict §§1–4. Thus the obstruction already occurs on this fixed seven-row calibrated original COMMON menu, over every admitted finite positive alternative core and one shared tuple.

The scope excludes full C/D-retaining data, exposed IDs/controls, additional rate/register constraints, timed/ranked channels and INDEPENDENT/BOTH. This is the compiler's exact old restricted observation contract, not a new assumption on the full G3 problem.

## 6. Prior relation and exact remaining gap

The accepted October6 rational-classifier proof used a two-parameter positive-drift residual surface at cap7. The present reduction reuses its rational-density, inverse-suffix, boundary-atom and rational-root arguments unchanged in substance. Its extra drift relation was unnecessary for the degree contradiction; the accepted October2 zero-drift cap6 NO supplies the lower-cap target. This is a minimal new deduction from old accepted suppliers, not a new nonsemialgebraicity method.

It is stronger than merely showing a closure NO or unbounded cap-only witness counts. It is logically separate from robust NO holes: X(w) is in actual closure, and rational YES and NO both approach it. No open NO ball around it is asserted.

The decisive qualitative gap remains an input-dependent exact classifier of the cap6 image (and then the wider original G3 interfaces). A fixed semialgebraic image/formula is now ruled out even at this cap. A varying-complexity finite-certificate method could still work. Neither the supplied-node critical-image tests nor the regular Poisson acquisition certificate covers every input; failure of either is not NO. No total recognizer or undecidability claim follows.

## 7. Immutable source pins

All bodies were read, not inferred from filenames. The retained source map records exact Git blobs and byte hashes.

- DYADIC-POISSON-SHARP-CAPS.md: commit33da55b84df3bcdbdf627005049879a038597e08, research/2026-10-01-sol61-g3-boundary-resume-2124z/; blob c0fde3337fcd6be1b0fd1618d87d041e017ee4e7; §§1–2,3–6,9.
- Independent G3-DYADIC-SHARP-CAPS-REVIEW.md: archived at27b143c73a4ac272b560b2974d83ff96df738531, research/2026-10-01-sol61-head-audit-1956z/; blob9bfbe9b8083190f559b46f58c5a6cf01a9727226. Explicit all-r/flag statement and cap6 rational-count conclusion.
- NO-FIXED-SEMIALGEBRAIC-RATIONAL-CLASSIFIER.md and INDEPENDENT-RATIONAL-CLASSIFIER-REVIEW.md: commitca0aafa7092ffcaeb74db91c0f22e60c4e8640c2, research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/; blobs1eded68f39d75f53c73cfafddab8839776057200 and21cd41c89ba3086073ff3cf0f35bf3bfef35e694.
- CALIBRATED-FULL-MARGINAL-COMPILER.md and INDEPENDENT-FULL-MARGINAL-COMPILER-REVIEW.md: sameca0aafa commit/directory; blobs063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28 and5e04efe79d1e431cf3f8ca6350f8e4bb1c395a97.
