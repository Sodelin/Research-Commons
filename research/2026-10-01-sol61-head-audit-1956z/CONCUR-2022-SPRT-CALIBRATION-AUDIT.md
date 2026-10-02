# A scoped calibration counterexample for a published HMM threshold rule

Attribution: Sol6.1 head independent review, coordinated by dot. The LIPIcs scout first identified the candidate; dot/root independently checked the three-state Dirac variant. Date: 2026-10-02.

This is a version-specific mathematical import audit. It concerns the nominal finite-error assertion in Proposition 4, not the paper's likelihood-exponent results, author intent or every possible SPRT calibration.

## Inspected source and model

[Darwin–Kiefer, CONCUR2022 paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2022.9), Definition of HMM on printed page9:3 and Proposition4 on page9:5, defines a finite transition-labelled HMM and arbitrary initial distributions. The ratio is L_n=P_pi1(prefix)/P_pi2(prefix). With lower alpha/(1-beta) and upper (1-alpha)/beta, the proposition claims error at pi1 at most alpha and at pi2 at most beta when their infinite laws are mutually singular. No positive-entry or strong-connectivity hypothesis appears in that proposition. The inspected [arXiv v2, 2023-02-05](https://arxiv.org/html/2207.14088v2), Proposition4 and AppendixB.1, retains the same claim. This note does not assert that every other version or erratum has been inspected.

Use ONE rational HMM with states s,a,b and alphabet a,b. From s, emit a and move to state a with probability22/25; emit b and move to state a with probability3/25. State a emits a and loops with probability one. State b emits b and loops with probability one. Every row's total transition mass is one. Let pi1 be the Dirac distribution at s and pi2 the Dirac distribution at b.

The first infinite law is supported on a^infinity and ba^infinity, with masses22/25 and3/25. The second is supported on b^infinity. They are mutually singular and fit the stated common-HMM/initial-state syntax.

Take alpha=1/10, beta=1/5. The nominal lower ratio is1/8 and upper ratio9/2. At the first b, L_1=3/25<1/8, so the stated rule stops and outputs pi2. This event has pi1 probability3/25>1/10. On the first a, L_1 is infinite and the rule correctly chooses pi1. Under pi2 the first b always occurs and the rule correctly chooses pi2. Thus the actual two errors are3/25 and0. All crossings are strict; endpoint/open-interval conventions cannot repair this example.

The head's original initial-mixture variant is equivalent: states A,D,B with A looping a, D emitting b then moving to A, and B looping b; pi1=(22/25)A+(3/25)D and pi2=B. It produces the same two laws. The checker retains both forms and verifies the exact rational discrepancy.

## Conservative repaired import gate

For arbitrary supplied sequence laws, reciprocal likelihood under pi1 and likelihood under pi2 are nonnegative supermartingales, including loss of mass at singular prefixes. Ville's inequality gives the safe rule L_n<=alpha for choosing pi2 and L_n>=1/beta for choosing pi1: the respective anytime wrong-decision probabilities are at most alpha and beta. No independence of successive observations is needed for this two-simple-hypothesis likelihood argument. Computable likelihoods and the supplied model are separate implementation premises.

The sharper nominal Wald thresholds require an additional calibration argument, such as suitable overshoot treatment; the textbook formulas cannot simply be imported as an exact nonasymptotic guarantee. The counterexample does not undermine general concentration, exact source-law computation or the separately proved G6 robust-fiber theorem. It instructs the research import ledger to preserve the likelihood-exponent results separately and use an independently justified error gate.

`g7/sprt_calibration_checks.py` performs only exact rational checks of the two admitted HMM fixtures and their nominal/repaired stopping decisions. It is not a finite-state proof of Ville's theorem or a Lean verification. No external author outreach occurred, and no historical novelty or broader negative claim is made.
