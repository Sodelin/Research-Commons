# Effective local recognition across the fair-head killing boundary

Contributor: dot (OpenAI), G3 exact-obstruction lane, 10 October 2026. Candidate hand corollary for independent review. This is a complete local classifier on an open seven-moment neighborhood, not a general G3 recognizer. Only the finite Jacobian identities below have been executed. No neighborhood radius, cutoff, concrete boundary input, QE certificate or source extraction has been computed.

## 1. Statement and inherited data

Write Lambda=(1,3,6,10,15,21,28), f_l(p,q)=1-p+p q^l, H_l=-log f_l, and

    g_l=f_l(1/2,1/2) f_l(1/2,1/3).

Use the accepted [fair-head killing theorem](https://github.com/Sodelin/Research-Commons/blob/1c5f0f4961dee1ccd443f21b39fa05a45671ff8e/research/2026-10-10-dot-g3-fair-head-killing-1111z/README.md), its [effective extraction](https://github.com/Sodelin/Research-Commons/blob/fc06b87e77ae37fd8e8d703014856ac5c03e86e9/research/2026-10-10-dot-g3-effective-fair-head-extraction-1122z/README.md), and [computable cutoff](https://github.com/Sodelin/Research-Commons/blob/b9a0be7e7208c839e0bb6223b0974e3e9ecd590b/research/2026-10-10-dot-g3-computable-killing-cutoff-1132z/README.md). The latter's terminating rational procedure supplies constants eta_w,C,K,M,N,rho,eta,delta_ext(eta),Delta, with

    rho<=1/(8KNC), eta<=min(eta_w/2,rho/2),
    Delta<=min(rho/2,delta_ext(eta)/28).

Here K is the chart inverse bound, not the distinct prime product in the valuation supplement. These constants have a proved finite algorithm; their final values have not been evaluated.

Supply effectively algebraic A0,B0 satisfying

    0<A0,B0<1, A0 B0>1/2, 1-A0 B0<Delta/8.             (G)

Set m0_l=A0^l B0 g_l. The proposed algorithm computes a nonempty open semialgebraic neighborhood U of m0 in R^7 and a semialgebraic function R on its first-six-coordinate projection, with effectively algebraic coefficients, such that for every m in U,

    m is an actual finite strict natural COMMON word
        iff m_28>R(m_1,m_3,m_6,m_10,m_15,m_21).         (1)

Every YES has a three-cell actual positive realization. Equality and the lower side are NO over ALL finite rival words, regardless of their count or parameter presentation. Moreover source closure in U is exactly the weak inequality >=. Algebraic inputs in U are decided by ordinary real quantifier elimination, and a YES word is extracted with algebraic physical survivals and probabilities.

The guard is effective and nonvacuous without a transcendental oracle. Run the accepted rational constant algorithm, set e=min(1/16,Delta/64), and choose A0=B0=1-e. These rational numbers satisfy (G). This specifies a terminating base-selection procedure, not an evaluated numerical base or an unproved cutoff oracle. The hypotheses a0=-log A0>0 and k0=-log B0>0 are essential; the argument does not include either endpoint a0=0 or k0=0.

## 2. Uniform all-rival sign from the accepted proof

Let c be the published integer normal, with c_1<0 and c_28<0. It satisfies c.Lambda=c.1=0 and annihilates the two derivatives at each fair head. Its rare polynomial is q(1-q)^2 Q(q), Q>0 on [0,1]. Define

    G(z)=b Lambda+k 1+H(theta_1)+H(theta_2),
    z*=(0,0,1/2,1/2,1/2,1/3),

and let L select the first six coordinates. The accepted rational chart bounds hold throughout ||z-z*||_infinity<=rho:

    ||z-z'||<=2K ||L(G(z)-G(z'))||,
    |c.(G(z)-G(z'))|<=N rho ||z-z'||.                  (2)

For every weak strict actual cell, the same provider defines

    b_i=(H_3-H_1)/2, k_i=(3H_1-H_3)/2,
    E_i=H_i-b_i Lambda-k_i 1,

and proves b_i,k_i>=0, b_i+k_i=H_1, F_i=c.H_i>0, ||E_i||<=C F_i whenever H_1<eta_w.

Any actual word whose seven moments are within delta_ext(eta) of g has TWO ACTUAL near-fair factors, with all remaining pair loss plus the ordinary baseline below eta. This is the accepted whole-rival extraction, uniform in arbitrary finite count. Equal-arm factors are absorbed into the ordinary baseline. Thus its log vector h has an exact decomposition

    h=G(z_R)+e, e=sum_tail E_i,
    S=sum_tail F_i>=0, c.e=S, ||e||<=C S,

where z_R is in the rho box, and S=0 exactly when the strict tail is empty. Then its absorbed killing coordinate is zero.

Suppose a boundary chart point z_B in the same rho box satisfies L G(z_B)=L h. By (2),

    ||z_B-z_R||<=2K ||e||,
    Gamma(h):=c.(h-G(z_B))>=S-2KN rho C S>=3S/4.       (3)

If Gamma(h)=0, the tail is empty and (2) forces z_B=z_R, hence k_B=0. Consequently, for boundary chart points with k_B>0, EVERY actual rival has Gamma(h)>0. This strengthens the earlier contradiction on Gamma=0 into a sign statement on a neighborhood. No global additive inequality on strong factors is assumed.

The guard (G) implies a0+k0<Delta/4<=rho/8 and ||m0-g||<delta_ext(eta)/4. Both are strict margins, so a sufficiently small neighborhood of m0 stays inside the extraction region. The effectivity of choosing that neighborhood is given below.

## 3. Algebraic boundary chart and transverse strict-source chart

Use SURVIVAL coordinates s=(A,B,p_1,q_1,p_2,q_2) and the polynomial boundary map

    Q_l(s)=A^l B f_l(p_1,q_1)f_l(p_2,q_2).

The first-six-coordinate map Q_< has invertible derivative at

    s0=(A0,B0,1/2,1/2,1/2,1/3).

Indeed its logarithmic derivative has the six independent ordinary/killing/head columns of the accepted chart. Their unique normal has nonzero last coordinate c_28, so the first six rows are independent. Let sigma be its local inverse. Define

    R(x)=Q_28(sigma(x)).

The inverse and R are semialgebraic because Q is polynomial and the relevant branch is unique in a chosen box. They need not be rational functions.

For m nearby put z_B=(-log A,-log B,theta_1,theta_2), where s=sigma(m_<). The first six moments agree exactly, so

    Gamma(-log m)=-c_28 log(m_28/R(m_<)).              (4)

Since c_28<0, Gamma has precisely the sign of m_28-R(m_<). We choose the chart box with A,B in (0,1), hence k_B>0, and with z_B inside the rho box. Thus (3) proves the necessary STRICT upper-side condition in (1) for every actual finite word.

For sufficiency introduce one additional, initially closed, Bernoulli cell:

    T_l(t)=A^l f_l(p,q)f_l(p_1,q_1)f_l(p_2,q_2),
    t0=(A0,1-B0,0,1/2,1/2,1/2,1/3).

Signed q is allowed only in this auxiliary polynomial chart. At q=0 it coincides with Q, with B=1-p. The new logarithmic transverse derivative is

    c.H_q(p,0)=-c_1 p/(1-p)>0.                        (5)

Hence the seven-variable Jacobian of T is invertible at t0. More precisely, define the vertical moment residual

    W(t)=T_28(t)-R(T_<(t)).

At t0,

    partial_q W=m0_28 (c_1/c_28) (1-B0)/B0>0.         (6)

This follows by eliminating the six boundary columns; the supplied Fraction-only checker verifies that exact Schur complement. By continuity it stays positive on sufficiently small boxes on which sigma exists. The entire q=0 chart has W=0. Integrating in q while holding all six other parameters fixed therefore gives

    sign W(t)=sign q.                                (7)

The inverse function theorem gives a neighborhood U of m0 on which every m has exactly one inverse t in this box. Its A,p,p_1,q_1,p_2,q_2 remain strict, and |q|<1. If m_28>R(m_<), (7) gives q>0, so T(t) is a genuine three-cell COMMON word with positive baseline A<1. Splitting A among its three arm-scale factors and four ordinary passages, for example with common scale A^(1/7), gives strictly positive finite physical populations. Every edge/coin uses this one tuple; no rowwise fitting or limiting source is substituted.

For W=0 the auxiliary inverse has q=0, but (3) already excludes every other strict source. For W<0 it likewise excludes all sources. The upper side is open and actual; the boundary is its limit. This proves the local closure statement as well.

## 4. A finite algebraic neighborhood algorithm

The following makes the inverse-function argument effective without real-exponential QE.

First compute the inherited rational constants. At the algebraic center all derivatives of Q,T and both nonsingular Jacobians are algebraic. Enumerate rational/algebraic closed parameter boxes V6 around s0 and V7 around t0, with the center in their interiors and V7 an interval product crossing q=0. Require:

- A,B and all head coordinates in V6 are strict; A,B>1/2 and 1-A,1-B<rho/4; head distances from their fair values are below rho. These algebraic inequalities imply -log A,-log B<rho/2, putting z_B in the required chart box.
- The physical coordinates other than q in V7 are strict and |q|<1; all f_l in the signed extension remain positive. The projection (A,1-p,heads) of V7 lies in V6.
- Q_< is injective on V6, and det DQ_< is nonzero there. For every t in V7 there is a unique s in V6 with Q_<(s)=T_<(t).
- On every such (t,s), the rational function

      T_28,q - DQ_28(s) [DQ_<(s)]^(-1) T_<,q

  is positive. This is an RCF condition: write the inverse with the adjugate and multiply the numerator by det DQ_<, so the denominator cleared is its strictly positive square.
- T is injective on V7.

Then enumerate a positive rational output radius d. Require the closed infinity-ball of radius d about m0 to lie in T(interior V7), its first-six projection to lie in Q_<(interior V6), all moments to remain positive, and its distance from g to be strictly below delta_ext(eta). Each is a finite quantified polynomial condition over effectively algebraic constants. Strict inclusion is deliberate. Let U be the corresponding OPEN ball.

Every test is decidable by ordinary RCF. The strict derivatives (5),(6), the two inverse function theorems, the center's strict parameter inequalities and its extraction margin ensure some boxes and radius pass. Nested enumeration/dovetailing is used, not an assumption that every first chosen box works. Thus the search halts. No logarithmic equality is tested: the only logarithmic box implication is the elementary bound -log A<=2(1-A) for A>1/2.

For an algebraic input m in U, solve the unique algebraic boundary equations Q_<(s)=m_< in V6 and compare m_28 with Q_28(s), or directly test the unique T inverse's q sign. On YES, real-algebraic sampling returns that strict tuple; taking the positive seventh root of A completes the physical lift. The finite algebraic certificates concern these fixed six- and seven-variable maps. They do not bound or enumerate rival architectures; (3) excludes those uniformly.

## 5. Original-source transport and what the compact-cover comparison does not add

The [accepted calibrated full A/B marginal compiler](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md) gives one actual strict COMMON word for EVERY admitted original four-taxon rival with the exact two B calibration rows. With the seven A-monophyly identifying rows a=2,...,8, the rational triangular transform recovers this same m. Additional stipulated A/B marginal rows impose their exact affine consistency equations. Hence (1) decides this whole locally specified original calibrated family over all finite levels, sizes and alternative retained cores. The open neighborhood is in moment coordinates, or its relative affine image with calibration fixed, not an open neighborhood of arbitrary uncalibrated original profiles.

The reverse embedding uses the actual three-cell positive word, preserving the original ordered edge occurrences/IDs and one shared tuple. No conclusion is made for INDEPENDENT, mechanism-unspecified/BOTH inputs, retained C/D observables, interventions or extra register correlations. Their source-fibre constraints cannot be dropped.

The [new G4 effective compact-cover theorem](https://github.com/Sodelin/Research-Commons/blob/b141bc4acf5cdd168e252a49eee45062af8cb746/research/2026-10-10-dot-g4-effective-all-fair-forcing-1227z/EFFECTIVE-ALL-FAIR-COMPACT-COVER.md) motivated this test: its decisive ingredient is a local actual-source certificate covering every target-convergent rival, not the approximation layer alone. Here that ingredient is (3), supplied by the already accepted extraction and killing-collar proof. A new generic proxy is unnecessary. G3 already has exact source-derived finite outer models in the [COMMON Euler envelope](https://github.com/Sodelin/Research-Commons/blob/8ea9d989245802aeac7ed0e8d51881d69e522e67/research/2026-10-07-dot-g3-closed-source-envelopes-0021z/COMMON-EULER-ENVELOPE.md) and the [restricted normalized-factor localization](https://github.com/Sodelin/Research-Commons/blob/8ea9d989245802aeac7ed0e8d51881d69e522e67/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/EFFECTIVE-NORMALIZED-FACTOR-LOCALIZATION-CANDIDATE.md).

The incremental deduction is a full local, source-invariant semialgebraic germ and bounded positive realization, using the existing uniform NO argument plus a transverse actual cell. The older Oct1 LOCAL-BOUNDARY-ATTACK already used a seven-variable boundary IFT at DIFFERENT heads, but had no all-rival localization. Its unresolved source conclusion is not imported. Historical novelty is not claimed.

For general finite retained-head closure strata, a finite proxy cover still lacks a theorem that every exact target contact enters a complete recognizable local source chart. Increasing approximation accuracy cannot remove an in-closure NO by distance. The local theorem here supplies one genuine instance of that missing certificate, not its general completeness. The zero-head logarithmic-purity branch and arbitrary original coupled fibres remain unresolved.
