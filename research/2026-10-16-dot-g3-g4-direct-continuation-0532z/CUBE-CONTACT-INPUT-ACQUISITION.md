# Acquiring the four-normal certificate from the algebraic input

Contributor: dot, 16 October 2026. Status: hand candidate, not reviewed or executed. This is a proposed input-only application of established multiplicative-relation algorithms and real algebraic decision to the newly checked four-normal template. It is not a general recognition algorithm or a new transcendence theorem.

## 1. Precise output

Input is a tuple m of twelve positive effectively real-algebraic observations in (0,1), indexed by Lambda=(1,3,6,10,15,21,28,36,45,55,66,78). The algorithm returns either:

- a checked four-normal small-loss certificate, an algebraic root parameter r in (0,1), and algebraic margin data, followed by the exact private-chain YES/NO decision on that certificate's domain; or
- TEMPLATE_UNAVAILABLE, which has no implication for source membership.

No r, normal bank, small-loss cutoff, source size, or Poisson representation is supplied as input. The algorithm terminates because it computes a finite multiplicative-relation basis and decides one fixed-format real-algebraic formula. Its completeness is only for the explicitly defined certificate predicate below. It covers the sufficiently-small-loss r=1/2 instances already established, but not arbitrary original fibres.

## 2. Existing arithmetic supplier

Compute a Z-basis e_1,...,e_t of

L(m)={e in Z^12: product m_lambda^e_lambda=1}.

This is established effective algebraic-number theory. A current primary exposition is Sertoz, Ouaknine and Worrell, [Computing transcendence and linear relations of 1-periods](https://people.mpi-sws.org/~joel/publications/1-periods25.pdf), author-hosted 54-page version read16 October2026, Lemma8.8.61 on page43. It explicitly reduces the relevant logarithmic relation computation to effective multiplicative relations, citing van der Poorten–Loxton1977 Theorem1 and Masser1988 Section4. Baker's theorem identifies algebraic-coefficient logarithmic relations with the algebraic span of the rational ones. Only this established linear/logarithmic result is used; no general equality of polynomials in logarithms is assumed decidable.

For any real coefficients alpha_j, every row c=sum alpha_j e_j satisfies c.h=0 for h=-log m, because each e_j.h=0. Conversely, if c is algebraic and c.h=0, Baker's theorem places c in the algebraic span of this lattice. Positive real arguments make the real logarithm unambiguous; there is no unnoticed 2pi i branch.

The earlier [algebraic-residue critical census](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-critical-arithmetic-census-1148z/INPUT-ONLY-ALGEBRAIC-CRITICAL-CENSUS.md) already uses Baker/projective arithmetic at its different critical-presentation scope. The arithmetic principle is reused, not claimed anew.

## 3. One finite certificate predicate

Use variables r in (0,1), four coefficient rows c0,c1,cA,c2, and their lattice expansion coefficients alpha. Constrain each row to span_R L(m). Require the same zero padding, normalization F(0)=1, ordinary-neutrality, and double-root equations as in [the four-normal proof](https://github.com/Sodelin/Research-Commons/blob/4ded3198196428f4dbb6e4b19db8f8f16da3e521/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-FOUR-NORMALS.md), now at this variable r:

F0 roots {1,r,r^3};
F1 roots {1,r,r^2,r^3,r^6};
FA roots {1,r,r^2,r^3,r^4};
F2 roots {1,r,r^2,r^3,r^4,r^6}.

All are polynomial equations: powers are fixed natural exponents. The sparse Descartes and order-table proofs hold for every 0<r<1, since these powers are distinct and their first missing orders do not change.

Add the following variables and verification inequalities, precisely following [effective cutoff acquisition](https://github.com/Sodelin/Research-Commons/blob/dd02cfb5067a3b9e7d7d445a886bec4d6224ee96/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-EFFECTIVE-CUTOFF.md):

1. A number Q with r<Q<1, five disjoint closed intervals strictly inside (0,Q), with each r^j strictly inside its own interval, j=1,2,3,4,6; positive mu for each row; and B>=1 bounding the sum of absolute row coefficients (use auxiliary absolute-value upper bounds).
2. For each row, the endpoint inequality L_qq >= mu p(1-p) on 0<=p<=1 and Q<=q<=1. Here L_qq is the explicit rational function in Section2 of the effective proof, not a logarithm in the formula. Multiply by the product of the positive D_lambda^2 denominators. Its integration justification is inherited; the inequality itself is polynomial.
3. On every root interval, positive a and, for odd first-missing k, positive b, and M>=1 satisfying F(q)>=a(q-q0)^2; |F(q^j)|<=M(q-q0)^2 for2<=j<k; and F(q^k)>=b for odd k. For nonroot intervals and the closed complement, positive lower bounds delta for F. Each condition is a finite universal polynomial inequality on a declared interval or finite union of intervals. Absolute values are represented by two inequalities.
4. Positive z0<=1/2 and p0<=1/3, with p0<=z0/2. For every root interval impose 4Mz0<=a; for odd k impose 4kBz0<=b. For every nonroot/complement bound impose 4Bz0<=delta. These certify the exact series bounds without a transcendental predicate.
5. Choose H>=1 large enough that every retained positive order-table coefficient is at least1/H and every negative coefficient magnitude is at mostH. Concretely impose H b>=2k for odd root orders, H delta>=2 for positive nonroot orders, and H>=2^(k+1)B for every even root order. Then all four aggregate budgets hold with K=H^2.
6. Introduce C>0 satisfying

C<=1,
2C<=(1-Q)p0,
1576 C H^18 <= 1-Q,
2(1-m_1)<C.

The first three inequalities ensure C is no larger than the effective cutoff constructed with K=H^2 and W*=1/(788H^18). The last is precisely the strict observed-data small-loss gate.

There are only four rows, five node intervals, and orders k<=5; every quantified variable list and polynomial degree is finite and fixed apart from the computed rational lattice basis. The sole appearance of observed values is algebraic, including m_1. No log(m), unknown source factor count, integer exponent variable or real-power expression occurs in this RCF formula.

## 4. Soundness and actual algorithm

Decide the finite formula over the real algebraic coefficient field of the input. If false, report TEMPLATE_UNAVAILABLE. If true, sample an algebraic witness and verify its finite inequalities. Real-closed-field sampling is valid because all coefficients are algebraic, even though the initial formula allowed real variables.

The four rows annihilate the actual logarithmic observation vector by their lattice-span equations. The universal derivative inequalities, local polynomial bounds and geometric series estimates prove the same strict-factor table as before. The H-based choice gives all four count-uniform budgets with K=H^2. The input gate implies -log m_1<C, and the explicit absorption removes every strict Bernoulli factor from any hypothesized source. Thus private-chain membership is equivalent to all ordinary equations m_lambda=m_1^lambda, decidable algebraically. These equations produce a strict ordinary witness when true and an all-finite-word exclusion when false.

The original calibrated COMMON corollary transfers this decision to the precise fourteen-row all-core menu when its identifying rows and exact B calibrations are present. It does not allow an algorithm to request missing G3 rows or replace retained C/D channels.

## 5. Completeness, examples, and remaining obstruction

This is complete for the displayed margin-certified template: if its constraints have any real solution, the RCF algorithm finds an algebraic one. It is also complete relative to any algebraic four-normal certificate satisfying these exact numerical margin inequalities, because Baker places its rows in the computed lattice span. It does not assert that these conservative margins include every tuple for which some stronger analytic proof works.

For fixed rational r=1/2, the published theorem and effective construction provide rational rows and margin constants. The algebraic family m_lambda=b^(lambda+R_lambda(1/2)+R_lambda(1/8)), with b rational sufficiently close to1, annihilates every row. Each rational row has an integer multiple in L(m). Its fixed margin certificate therefore satisfies this input-only formula once b is sufficiently close to1. Hence the procedure has a nonempty sound original-NO domain and does not require the parameter r to be given by the caller.

If L(m) has rank zero, this template is unavailable immediately: a normalized nonzero row cannot lie in its span. More generally, the method acquires only normals that can be represented in this computable algebraic relation space. It does not decide the earlier nonlinear logarithmic purity test, exclude transcendental normal/residue strata, handle arbitrary retained heads or shared-register fibres, or prove complete negative-certificate coverage. The input-dependent lattice also means this is not one fixed semialgebraic classifier in the numerical observation coordinates; existing fixed-classifier limitations are not contradicted.

General G3 OPEN. General G4 OPEN. No relation lattice, RCF solver, source model or numerical cutoff was executed for this note. Historical novelty is unresolved; the candidate contribution is the exact finite acquisition adapter for the four-normal template, with the classical arithmetic and real-algebraic machinery explicitly credited.
