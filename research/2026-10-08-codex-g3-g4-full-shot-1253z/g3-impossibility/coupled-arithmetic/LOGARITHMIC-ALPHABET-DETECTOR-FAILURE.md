# A source countercontrol to the exposing-residue logarithmic alphabet design

Contributor: Codex, original G3 attempt 3, 8 October 2026. **Hand-derived global route obstruction submitted for root review.** This checks an algebraic encoding device, not another finite-cap numerical diagnostic or a full G3 result.

## Proposed detector and exact physical source

Let Lambda be any finite set of distinct positive integer exponents admitted as COMMON survival moments. Choose real coefficients c_lambda with ordinary neutrality

    sum_lambda c_lambda*lambda=0.

For one normalized COMMON factor f_lambda=1-p+p*q^lambda, define its additive score

    H(p,q)=sum_lambda c_lambda log(1-p+p*q^lambda),
    P(z)=sum_lambda c_lambda (z^lambda-1).

An actual strict one-bigon word has moments A^lambda*f_lambda, with 0<A,p,q<1. Split A into positive leading, arm-scale and connector populations by the inherited normalization. Ordinary neutrality cancels the lambda*log A contribution exactly. Thus H is the score of a literal actual strict source cell with padding, not an arbitrary moment mixture.

The candidate encoding chooses a nonzero P>=0 on (0,1), with interior zero residues, and assumes H>=0 for every strict source factor. Then a zero observed additive score is supposed to force every hidden factor to belong to those residues. The latter nonnegativity premise fails.

## Lemma

If H(p,q)>=0 for EVERY 0<p,q<1, then either all c_lambda=0 or P(q)>0 for EVERY q in (0,1).

**Proof.** At each fixed q, analyticity at p=0 gives

    H(p,q)=p*P(q) - (p^2/2)*[P(q^2)-2P(q)] + O(p^3).    (1)

This is the expansion of log(1+p*(q^lambda-1)); the factor one half in its second coefficient is essential. Nonnegativity for all sufficiently small positive p implies P(q)>=0.

Suppose P(q_0)=0 at an interior q_0. Equation (1) then begins with −p^2*P(q_0^2)/2. Since P(q_0^2)>=0, nonnegativity forces P(q_0^2)=0. Applying the same argument at q_0^2 gives P(q_0^4)=0, and inductively P(q_0^(2^j))=0 for every j. These are infinitely many distinct real zeros of one finite polynomial. Therefore P is identically zero. Its distinct positive powers have coefficients c_lambda, so every c_lambda=0. This proves the lemma.

Equivalently, for any nonzero nonnegative exposing P with an interior root, let j be the first positive integer with P(q_0^(2^j))>0; such j exists because a nonzero polynomial has finitely many roots. Put q=q_0^(2^(j-1)). Then P(q)=0 and P(q^2)>0. Equation (1) gives H(p,q)<0 for all sufficiently small positive p. Choosing any positive normalized baseline A and the actual strict padding realizes this violating factor in the original source class. No zero population or deterministic natural coin is used.

## Exact consequence and limits

One cannot take a sparse nonnegative exposing polynomial with chosen strict residue zeros and turn it directly into a globally nonnegative additive log score on COMMON source factors. The first-order rare-coin expression misses the negative second-order correction. The actual positivity class contains that correction.

The lemma does NOT prove that every globally nonnegative logarithmic score has no zero at an interior pair (p,q); it proves only strict positivity of its first-order polynomial P on strict q when the score is globally nonnegative. It does not cover coefficients depending on protected parameters without a separate fixed-parameter argument, nonlinear source statistics, nonlocal coupling, or a complete arithmetic reduction. A literal zero score at a finite interior pair could require further analysis. General original G3 remains open.

This is an elementary analytic consequence of the original factor law. No historical novelty, formal verification, numerical cutoff, solver or execution is claimed. The source law, positive normalization and finite-atomic/exposing machinery are governing prior, not newly introduced biological operations.
