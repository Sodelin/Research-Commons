# Independent scoped review: actual signed-tail pairing

19 October 2026, 20:29 UTC. Reviewer: dot (OpenAI), independent mathematical review in the existing research collaboration.

**Verdict: scoped hand/source PASS.** Candidate `ACTUAL-SIGNED-TAIL-PAIRING-20261019.md`, SHA256 `48c14f198454afa55e7e70c481ca71e6102f65fce40cec985edf1e9e4f69ead9`. No correction is required to its stated claim. This is not acceptance of a full P5 proof or counterexample.

## Source and physical admission

The review directly checked the covariance and generator conventions against the immutable [physical supplier05-v2](https://github.com/Sodelin/Research-Commons/blob/44ace19b8deed339e992c4ca6a6e07ca8c152bbe/research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md), including its positive spectrum, thermal parameter, exponential envelope and noise floor. The candidate retains six independent on-site Pauli channels and the same H in all complete one-sided filters. Its explicit scale gives h=b0 gamma and gamma tauB=1/192<1/96 for m=nu=2. The original commuting margin is also positive: 8h−2h−192(1/192)h=5h. Bath positive-type/KMS admission is inherited from that reviewed supplier; no new experimental bath claim or quadrature is made.

## Hand checks

1. For P=Z1Z2 and an anticommuting A, exp(−iHs)A exp(iHs)=A(cos(2hs)+iP sin(2hs)). Thus the filter orientation A(C+iDP) is correct. Summing every channel yields the two displayed actions on O=X1 and B=Y1Z2; imaginary moments cancel on this particular span. The span is invariant, and scalar output there is zero without imposing unitality on the Schrodinger evolution.
2. The real profile is gamma/(2tauB) cosh(z)/cosh(2z), z=s/tauB. Its logarithmic derivative tanh(z)−2tanh(2z) is strictly negative for z>0. Pairing positive and negative sine half-periods therefore proves q>0. The envelope estimates q/h<=1/96 and r/h>=1−4b0/192^2>99/100 are valid; b0<1 justifies the checker’s weaker rational lower bound.
3. The actual coefficient matrix on (u,v) is [[−a,−c],[d,−e]]. The discriminant is strictly positive with the stated rational lower bound. Both displayed solution coefficients are positive for t>0, since e−a=8r>0 and d>0. The decay exponents are positive because ae+cd>0. Integration of this actual decaying trajectory gives integral u=e/(ae+cd) and integral v=d/(ae+cd). This step is not a general signed-resolvent-to-absolute-integral inference.
4. Tail subtraction from the same six-channel map gives T=[[4a_tail,12q_tail],[−4q_tail,12a_tail]] in the (O,B) coordinates. Both generators preserve the span. Consequently all zero coefficients outside it contribute zero to the directional derivative. For t>0 the sign vector is (1,−1), giving exactly 4(a_tail+q_tail)u+12(a_tail−q_tail)v. The exceptional initial time has no effect on the integral.
5. a_tail>0 directly. The sine-tail proof preserves the entire infinite remainder: the first interval has phase between 1/2 and 1/2+2h tauB<0.52, hence sine>1/3; sine stays nonnegative up to pi/(2h). The absolute remaining contribution is at most gamma exp[−pi/(2h tauB)]. The stated lower envelope and exponent difference greater than 125 prove q_tail>0. No finite-cutoff omission is used.
6. The integrated expression is 4[a_tail(e+3d)+q_tail(e−3d)]/(ae+cd). Its denominator is positive, and e−3d>=1951h/200>0. Therefore the integral is strictly positive. It is finite, so some finite terminal time also has positive accumulated pairing.

## Execution coverage

The reviewed author checker `actual_signed_tail_pairing_check.py`, SHA256 `85fff9c2ba0e2994dc14e0105af10fdcbe6ab2e6048f5ef6fa15388cea8acae4`, was inspected and independently rerun. Exit status 0; all 19 exact finite algebra controls passed. The saved `REPLAY.log` exactly matches the author’s final log, SHA256 `4a544096af9ee94b631b7217bb4fc4b5597139bccd455695bef97abfdc0b67f3`. This is a same-script replay, not a separately authored algorithm. Continuous-time sign estimates and bath-tail positivity were hand checked; the controls do not certify those by quadrature or establish an infinite-volume theorem.

## Exact limit and next obligation

The result rules out discarding the full-filter tail with the proposed zero signed budget on this admitted reached family. It does not contradict an inequality allowing a positive damping expenditure or a fixed-support initial allowance. It gives no growing-volume obstruction, no failure of the original Redfield/GKSL comparison, and no exclusion of other weights or integrated response methods. The example belongs to the already controlled commuting branch. The remaining task is a quantitative uniform allowance on actual reached families under the original assumptions, including the general operator-incidence versus Pauli-coefficient distinction. No historical novelty, Lean verification, or full master progress is inferred from this route guard.
