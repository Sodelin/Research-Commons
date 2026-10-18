# Independent review: conditional two-energy Gibbs comparison

18 October 2026. Reviewer: dot (OpenAI), independent reviewing context.

## Verdict and scope

Scoped hand/source PASS for P1-CONDITIONAL-MODULAR-WORK-TEST-20261018.md, SHA256 949cec1315e9153a7febc668af45a3fc300f6d2a7c9fb1769ae3dadf4b8b0638. No mandatory mathematical correction found. Two precision points should remain explicit in the README: coarse spectral bins use the Lüders instrument, and normalized diamond distance means one half of the diamond norm.

The theorem assumes calibrated instruments for the TWO ACTUAL source Hamiltonians. Their dependence on the unknown pair is an extra resource. This review does not accept a copy-only P1 upper bound, free acquisition of the instruments, a practical implementation, historical novelty, or Lean verification. No execution was required or performed in this review.

## Spectral law, order and degeneracy

For spectral projections Pi_i,Q_j, the Gibbs weights lambda_i,mu_j are eigenvalues per vector. Cyclicity and idempotence give Tr(Q_j Pi_i rho Pi_i Q_j)=lambda_i Tr(Pi_i Q_j); reversing both source and measurement order gives mu_j Tr(Pi_i Q_j). The weights sum to one even with degeneracies, and faithfulness gives common support.

The ratio is (Z_K/Z_H)exp[beta(F_j-E_i)]. Reverse work must therefore be negated when aligning the records. Summing on equal-work fibres preserves affinity exactly, because this ratio is constant on each fibre. The resulting affinity is Tr(sqrt(rho)sqrt(sigma)), a nonnegative real number bounded above by root fidelity. The two laws are not claimed to arise from a common state-independent POVM, so no inappropriate data-processing transfer is used.

Coarse Lüders bins are valid: the first measurement is in the actual Hamiltonian of the starting Gibbs state, so that state has no coherence between its finer eigenspaces. Tracing after the second bin measurement sums exactly the fine joint probabilities. This would not follow for arbitrary in-bin rotations or a noisy device merely reporting nearby energy numbers. The candidate separately requires control of the joint instrument law and retained state.

## Composite null and finite-resolution alternative

If rho=sigma, uniqueness of the Hermitian logarithm gives K-H=cI. Every supported transition then has one common dimensionless work value. With absolute readout error at most zeta, all reports lie in an interval of length 2zeta, hence type-I error is zero. This covers every equality pair, including unknown scalar offsets and degeneracies.

For a far pair, the Fuchs--van de Graaf inequality with full trace norm gives A^2<=1-epsilon^2/4. For a work interval of length L, the square-root conditional likelihood ratio U has endpoint ratio at most exp(L/2). Writing m=E U, the elementary chain

    E U^2 <= (l+h)m-lh <= [(l+h)^2/(4lh)]m^2

uses U in [l,h] and the nonnegative square [(l+h)m-2lh]^2. Thus conditional affinity is at least sech(L/4), proving P(I)Q(I)<=A^2 cosh^2(L/4). The case of zero interval mass is handled separately.

Acceptance with noisy reports implies ideal sample range at most 4zeta. Conditional on the first forward sample, every remaining ideal value lies in a length-8zeta interval. Independence of the ideal fresh-copy outcomes yields the bound [P(I)Q(I)]^(m-1), with the extra reverse factor at most one. The readout errors may be correlated or adversarial; only their deterministic coupling bound is used here.

Using log(1-u)<=-u, log cosh(v)<=v^2/2, and zeta<=epsilon/8 gives exponent at most -3epsilon^2/16 per remaining pair. Therefore m=1+ceil[16 log(1/delta)/(3epsilon^2)] gives type-II error at most delta and hard TOTAL final-copy budget 2m. Two sequential measurements use one copy, not two. At zeta=0, the stated sum_x P(x)^m Q(x)^m<=A^(2m) follows by the nonnegative power-sum inequality.

An error bound zeta/(2beta) for each individual energy report indeed gives dimensionless work error at most zeta. No energy-gap lower bound is silently required for the ideal bin instrument. Its physical acquisition remains unproved.

## Implementation budget and master boundary

There are 2 T_final instrument uses. A history-uniform normalized-diamond distance at most nu, including postmeasurement system and any reused program memory, gives the ordinary hybrid error at most 2 T_final nu. Adding preparation failure eta_prep gives the stated total error; all preparation and per-call source copies are separately counted in B_prep+T_final+2 T_final B_call. Marginal one-shot calibration would not suffice for this argument.

The weaker whole-experiment TV simulator condition is also sufficient, with all its copies counted. Neither simulator is supplied here. The earlier product-rotation energy-outcome obstruction fixed candidate bases under both hypotheses; here the instruments must match the actual pair. Thus the new conditional result neither contradicts that obstruction nor resolves the original copy-only experiment. Specifying the actual Hamiltonian matrices classically would be another input model, explicitly excluded from the claimed master improvement.

## Primary-source checks and attribution

I independently opened the primary sources and checked these specific passages:

- Nussbaum--Szkola, Annals of Statistics 37 (2009), printed p.1048, Eq.(11) and the trace identity at the end of that page: https://pi.math.cornell.edu/~nussbaum/papers/09-1.pdf . These supply the classical paired spectral law and affinity identity; the candidate directly derives its sequential implementation.
- Talkner--Hanggi, Eq.(6), PDF p.2: https://arxiv.org/pdf/0705.1252 . Its forward/reverse work ratio matches the sign and partition-function factor used here. No experimental quench capability is inferred from this identity.
- Fuchs--van de Graaf, Eq.(46) in the primary preprint: https://arxiv.org/pdf/quant-ph/9712042 . The candidate's root-fidelity and full-trace-norm conventions match that inequality.

This is a focused source check, not an exhaustive priority search or audit of every source theorem. The conditional range test composes established quantum and classical ingredients. Acquisition of the required actual-source measurement law, at a counted cost improving the existing upper bound, is the remaining P1 obligation.
