# Independent scoped review: coding increments and classical-output prediction

Date: 20 October 2026 (UTC).
Reviewer: dot, separate coordinating review for Nolan's research.
Candidate: P1-UNIVERSAL-CODING-PREDICTION-GAP-20261020.md.
Candidate SHA256: 12cabad2d80c55369914431d93c7089d5b983ff732cc4ee5526bbc4f53ef7a94.

## Verdict

Scoped hand/source PASS. The entropy identity, support conventions, posterior Bayes act, pure-Haar control and copy accounting are correct. No mathematical correction is required. This is an inspectable applicability check of a specific conversion from quantum coding redundancy to classical-output estimation risk. It does not prove a Gibbs, Bures, or decision lower bound, and it does not rule out coding methods with additional measurement analysis.

One presentation clarification is recommended in a publication wrapper: use “Umegaki relative-entropy prediction risk after measurement” rather than the potentially ambiguous “measured relative-entropy risk.” The latter can also denote the distinct measured-relative-entropy divergence. All equations in the candidate unambiguously use Umegaki loss.

## Independent algebra checks

For each nonzero-probability outcome, expand the logarithms and use the posterior mean mu to obtain the stated decomposition into posterior loss at mu plus D(mu||sigma). The support of mu contains every positive-posterior source support. The decomposition remains valid as an extended-real identity when sigma has insufficient support. Zero-probability outcomes can be discarded.

For finite prior and finite Hilbert dimension, R_D(Y)=S(B|Y)-s and delta_n=S(B|C)-s. Their difference is exactly I(B:C)-I(B:Y). Data processing under the measurement C to Y gives nonnegativity. Also the state B-label-C is conditionally product, so I(B:C)<=I(B:label)=chi_1. Taking infimum over all n-copy POVMs therefore proves Equations (1)-(3), including delta_n>=0. General outcome spaces replace sums by posterior expectations; no optimizer-attainment assumption is needed. If the sources share a supplied eigenbasis, measuring that basis on C preserves the already classical C register and the extra term vanishes.

With root fidelity f, 2(1-f)<=-2 log f<=D is the correct direction. Consequently a relative-entropy risk upper bound suffices for squared-Bures risk, while a relative-entropy risk lower bound does not lower-bound squared-Bures risk.

For the Haar example, the symmetric-subspace dimension ratio gives delta_n=log((n+d)/(n+1)). The posterior eigenvalues are (n+1)/(n+d) and 1/(n+d), repeated d-1 times. Their entropy gives the quoted risk and subtraction gives (d-1)log(n+1)/(n+d). The fixed-d ratio grows logarithmically. Reporting the measured ray instead yields Bures risk at most 2(d-1)/(n+d). This continuous, pure-state example lies outside both the finite-prior statement as written and the admitted faithful Gibbs family; it is correctly presented as a separate generic control, with the formulas independently specified.

Only C is experimentally measured. B is a mathematical loss register. There is no free queried future copy; the proposed two-source transfer would still use n copies from each input, totaling 2n. No such improved transfer rate is established here.

## Primary-source checks and depth

- Hayashi, https://arxiv.org/html/0806.1091v2 : directly read Section II, Eq. (9) and following bound, and Section III Theorem 1. The finite block domination coefficient and fixed-d asymptotic scope agree. Base conversion preserves the displayed form when the logarithm on the right is converted too.
- Tanaka, https://arxiv.org/html/quant-ph/0602072v1 : directly read the posterior definitions and Section III theorem/proof. The measurement is fixed before optimizing the predicted state. The alpha=0 normalized square-root mixture is stated correctly. The candidate appropriately does not use the problematic fidelity remark in Section IV.
- Tanaka and Komaki, https://journals.aps.org/pra/abstract/10.1103/PhysRevA.71.052323 : checked the published abstract only; no whole-paper audit is claimed.
- Hayashi, Dasgupta and Warsi, https://arxiv.org/html/2609.10072v1 : directly read the symmetric-projector/one-particle reduction and posterior formula, Theorem 16 proof and Eqs. (67)-(74). They support the arbitrary-POVM Haar optimum and the separate reported-ray overlap. This is a preprint supplier, not an admitted Gibbs construction or a priority certificate.

A useful boundary on the cumulative-coding discussion: for the consistent Bayesian iid mixture, strong subadditivity and exchangeability make delta_n nonincreasing; hence delta_n<=chi_n/n for n>=1. Thus cumulative bounds can give an increment upper bound with this extra argument. The candidate only rejects naive subtraction and the automatic conversion to measured prediction risk, so it is correct as written. Even this monotonicity argument does not remove Delta_meas or establish the sought M/n Bures rate.

## Publication and limits

A concise attributed publication is justified if its purpose is to prevent repeating this specific invalid operational conversion. Retain the explicit classical identities/prior attribution and the open measurement-level gate. No new master result, exhaustive prior survey, historical novelty, numerical or symbolic execution, independent benchmark, or Lean verification is certified by this receipt. No tactic or ownership change follows automatically.

## Publication successor diff review

The successor P1-UNIVERSAL-CODING-PREDICTION-GAP-20261020-v2.md was read and its exact diff checked. SHA256: e319d6a609b41b8f4926c34f94359fa6559a5bf7c30fda07b3e0285ef7095c42. Changes are the two terminology occurrences, the review-status sentence and the revision record. Mathematical content and copy/rate limitations are unchanged. The scoped PASS above applies to this successor. The original candidate remains preserved.
