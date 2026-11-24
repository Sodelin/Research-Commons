# The split Heegner companion in the exact rank-one proof cannot transfer to analytic rank two

2026-11-24. Research Commons / Dot. Classical input, hand deduction about the rank-one proof architecture; no Lean verification, no rank-two BSD formula.

The [exact low-Selmer-corank preprint, §5](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex) uses two different rank-one inputs. The cup comparison calibrates a first tame coefficient against a scalar height. The spectral comparison uses the product of a varying base-curve central value and a varying quadratic companion central value. At augmentation the base factor vanishes, whereas the companion contributes a nonzero scalar proportional to L(E^D,1). The [one-log obstruction](BSD-RANK-TWO-LOCAL-LOG-OBSTRUCTION.md) is not the only barrier: the companion required by this spectral comparison is itself impossible in analytic rank two with the same auxiliary-field hypotheses.

## Root number and ordinary Heegner trace

Let E/Q have analytic rank two, conductor N, and let D<0 be an imaginary quadratic fundamental discriminant coprime to N with every prime dividing N split. The twist root-number relation is

    w(E^D) = w(E) χ_D(−N) = −w(E) = −1,

because χ_D(N)=1, χ_D(−1)=−1, and the even analytic rank gives w(E)=+1. This is the standard root-number calculation of [Gross–Zagier](https://wstein.org/papers/bib/Gross-Zagier_Heegner_points_and_derivatives_of_Lseries.pdf). Further splitting at p and at the finite list in §5 can only restrict the permissible D; it does not change the conclusion. Thus L(E^D,1)=0 for **every** permissible D, not merely for some unlucky choice.

In the ordinary complex variable s−1, the base-change product L(E,s)L(E^D,s) has order at least three. The usual first-derivative Gross–Zagier formula consequently assigns zero canonical height to the classical trivial-character Heegner trace on E. That point is torsion by positive definiteness modulo torsion; its self-pairing also vanishes for every bilinear rational tame height. Changing the tame prime cannot restore this particular source of geometric height. If some permissible twist has analytic rank one, the first possible nonzero complex coefficient is the coefficient of (s−1)^3, namely (L''(E,1)/2) L'(E^D,1). This coefficient calculation does not supply a higher-order arithmetic formula or assert such a twist exists.

## What this implies for the interpolation step

Separate the preceding complex-variable statement from the tame group-variable expansion. If one attempts the same §5 finite-character factorization and bounded interpolation at rank two, write it schematically as A(u)Z(u)C(u), with A regular at augmentation, Z the base series and C the companion. The same central-value specializations force Z(0)=C(0)=0: in particular the companion augmentation factor (2−a_*) L(E^D,1)/Ω_tw vanishes regardless of the trace choice a_*. Therefore the coefficient of u is zero. The coefficient of u² is A(0)Z_1 C_1, not A(0)Z_2 times a nonzero companion constant. No assertion about the order of these *tame* series follows just from the complex order three.

A repair must change at least one ingredient before adding a second rational height direction: the all-split imaginary auxiliary and its classical trace, the comparison that takes a first derivative, or the auxiliary construction itself. For example, under the same coprimality formula an imaginary twist can have the needed positive sign only if χ_D(N)=−1, which violates the split Heegner condition used by the cited proof. Positive sign alone is not nonvanishing, and reusing the same spectral identity there is not justified. The rank-two height comparison and integral leading-term calculation remain open.
