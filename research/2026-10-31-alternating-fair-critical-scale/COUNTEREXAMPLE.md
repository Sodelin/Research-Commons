# Alternating strict fair reference cells refute generic critical-scale phase stability

31 October 2026. Construction and proof: dot (OpenAI-assisted research). Independent mathematical and original-source reviews were performed in the existing G4 and G3 contexts. The generic critical-scale question and canonical single-scale comparison family were proposed by Full Pro. This is a new bounded hand result, not Lean verification, a novelty determination or an original G3/G4 negative.

## Result

Fix the admitted positive budget H and L=H/4. On any fixed finite closed labelled-forest carrier used by the original equal-arm source, there are finite STRICT ALL-FAIR words K_j with exact COMMON hazard H and INDEPENDENT pair hazard 3H/4, but

    dist(L/h_j, integers)=1/2,
    ||[K_j,S_(h_j)]||=O_H(h_j^(9/2))=o(h_j^4).

The word, all site parameters and the reference are given explicitly below. Constants are independent of the growing finite word count. Thus no fixed positive alpha,kappa and finite C_H can make

    dist(L/h, integers) <= C_H[(||[K,S_h]||/h^4)^alpha+h^kappa]

hold uniformly over ALL such paired-clock fair words near h=0. The result does not concern the smaller image of ORIGINAL EXACT fitting/commuting sources under fairization, and does not produce an exactly commuting bad witness.

## 1. Retained original source and analytic fact

Use ROW matrices on the fixed CLOSED finite forest carrier, ordinary pair-rate-one generator Q and E(s)=exp(sQ), with s a duration. For s>0 define the ORIGINAL reference

    tau_*(s)=log(2-exp(-s)),
    w(s)=log(2exp(s)-1)=s+tau_*(s),
    S_s=E(s) B_fair(w(s)) E(2s-tau_*(s)).

Here B_fair is the actual equal-arm cell, routing each current root once with coin1/2 and then forgetting arm colours. In survival notation this is exactly E(t) B(t/(2-t),1/2) E(t^2(2-t)), t=exp(-s), as specified in the public original-source definitions:
https://github.com/Sodelin/Research-Commons/blob/7d21167021d6a2762ec283b800e6298deeec2139/research/2026-10-31-g34-hybrid-scalar-source-binding/SOURCE-DEFINITIONS.md

Its COMMON duration is4s, I-pair duration3s and cell gap s. Since0<tau_*(s)<s, both ordinary bookends and the fair arm duration are strictly positive.

The already public full fair third-jet argument supplies

    B_fair(u)=E(tau_fair(u))+O(u^3),
    S_s=exp(3sQ)+O(s^3).

Source: Section2, https://github.com/Sodelin/Research-Commons/blob/ba80d25ddd2d9ad6de54f5ea5835a315689f9a16/research/2026-10-31-g4-leading-prefix-channel/PROOF.md . Its explicit cubic operator is not needed here. The finite source matrices are analytic near s=0. Therefore the real analytic matrix logarithm F(s)=log S_s, defined in one fixed neighborhood ofI, has

    F(s)=3sQ+s^3 A_3+s^4 A_4+O(s^5),
    C(s)=F(s)/s=3Q+s^2 A_3+s^3 A_4+O(s^4).

A_3,A_4 are fixed finite matrices. There is NO quadratic term in F. No values of these matrices or new coefficient bank are required. Logarithms are finite-matrix proof devices, not physical operations.

## 2. Explicit strict family and both clocks

For each integer j>=1 set

    N=12j^2,  h=L/(N-1/2),  r=L/N,  a=h/(6j),
    s_+=r+a,  s_-=r-a,
    K_j=(S_(s_+) S_(s_-))^(N/2).

There are exactly N fair cells. Each factor occurrence is a DISTINCT finite physical site with its own original identifier; repeated numeric parameters do not reuse a hidden routing variable or turn the source into a loop.

The ratios satisfy

    r/h=1-1/(2N),  a^2/h^2=1/(3N),
    s_-/h >= 19/24 >0.

All ordinary gaps are positive; adjacent bookends may be merged without changing their chronology. Total reference duration is(N/2)(s_++s_-)=Nr=L. Hence the SAME physical tuple gives

    K_COMMON=E(4L)=E(H),  b2_I(K)=exp(-3L),
    total gap=L,  L/h=N-1/2.

The phase distance is exactly1/2. Also s_+/h and s_-/h both tend to1: no rare coin or relative-scale outlier is required.

For the admitted fixed H=(log2)/M with positive integer M, all s_±/H are positive rationals. Therefore t_±=exp(-s_±) are effectively algebraic, as are arm survivals t_±/(2-t_±) and right-bookend survivals t_±^2(2-t_±). Coins are exactly1/2. This assertion concerns survival parameters, not their duration logarithms; no short encoding-complexity bound is claimed.

## 3. The two moment cancellations

As j tends to infinity, h tends to zero, N=Theta_H(1/h), r=h+O_H(h^2), and a=O_H(h^(3/2)). In particular s_± are uniformly comparable to h.

There is an exact cubic cancellation:

    r^2+3a^2=h^2(1+1/(4N^2)),
    s_+^3+s_-^3-2rh^2=r h^2/(2N^2)=O_H(h^5).

For the quartic coefficient, write x=r/h=1-1/(2N). Then

    (r^4+6r^2 a^2+a^4-rh^3)/h^4
       =1/(2N)-7/(18N^2)+1/(16N^4)=O(1/N).

Thus s_+^4+s_-^4-2rh^3=O_H(h^5). Applying the Taylor expansion of F, including its uniform fifth-order remainder, gives

    X+Y=2r C(h)+O_H(h^5),
    X=F(s_+), Y=F(s_-).

Matching only the cubic term while discarding an uncontrolled fourth-order coefficient would be insufficient. The symmetric fourth-order calculation above is essential.

## 4. Ordered product error and the growing count

The common leading linear generator commutes with itself. Expanding X,Y,

    [X,Y]=3s_+s_-(s_-^2-s_+^2)[Q,A_3]+O_H(h^5)
          =O_H(a h^3)+O_H(h^5)
          =O_H(h^(9/2)).

No O(h^4) pair term remains. For sufficiently small matrices X,Y, the usual double-integral exponential-product estimate gives

    ||exp(X)exp(Y)-exp(X+Y)|| <= C||[X,Y]||.

The analytic logarithm is Lipschitz on one fixed small matrix ball aroundI. Consequently, defining only the SMALL PAIR logarithm

    G=log(S_(s_+)S_(s_-)),

we have

    G=X+Y+O_H(h^(9/2))=2r C(h)+O_H(h^(9/2)).

Now account explicitly for EVERY pair. Since N/2=L/(2r),

    (N/2)G=L C(h)+O_H(h^(7/2)).

The exact power identity is K_j=exp((N/2)G). We do NOT assert that this exponent is a chosen principal logarithm of K_j. Both exponents above lie in a bounded finite-matrix set, so Duhamel's estimate yields

    ||K_j-exp(L C(h))||=O_H(h^(7/2)).

The comparison matrix exp(L C(h)) commutes EXACTLY with S_h=exp(h C(h)). It is not claimed to be a physical source. Finally S_h-I=O(h), so

    [K_j,S_h]=[K_j-exp(L C(h)),S_h-I],
    ||[K_j,S_h]||=O_H(h^(9/2)).

Every constant is on the one fixed carrier/budget domain, independent of N. This is an actual growing-word estimate, not a fixed-word remainder extrapolated without paying its count.

## 5. Consequence and exact limits

Along this sequence, ||[K_j,S_h]||/h^4=O_H(h^(1/2)) tends to zero while the phase stays1/2. The proposed generic critical-scale inequality is therefore false for every fixed alpha,kappa>0 and finite C_H.

The earlier single-scale canonical family S_(L/N)^N had Theta_H(h^4) residual. That result remains valid: the present TWO-scale alternating construction is a different family, chosen to cancel the next source-moment mismatch. Exact fair rigidity is also not contradicted: the present words are only approximately commuting, not exact-return witnesses.

All-fair coins, paired clocks, finite strict words, effectively algebraic survival parameters, relative scales tending uniformly to the reference, and count of order1/h do not rescue the generic inequality. A source-specific theorem on the image of ORIGINAL EXACT fitting tuples would have to exclude these words by additional exact information. No such exact preimage is exhibited here; fairization fixes fair words only in the image of the larger arbitrary paired class. Additional protected IDs/ties or observations are not claimed preserved from any original fitting input.

This refutes an auxiliary quantitative implication, NOT original G3 recognition, AG-Pair, G4 forcing or a phase statement on exact fitting fibres. No new source engine, parameter search, bank, larger cap, physical run or Lean compilation occurred. A short exact symbolic check verifies only the displayed scalar cubic/quartic identities; it does not certify the analytic estimates or source assumptions.
