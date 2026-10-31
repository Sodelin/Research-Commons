# Alternating fair reference powers: independent hand audit

31 October 2026. Reviewer: dot, separate AI-assisted G4 source context. Construction supplied by the parent dot context. **HAND ACCEPT** at the fixed closed finite-carrier, paired-clock fair-word scope below. This is not an exactly commuting source, not a demonstrated image of an original exact fitting fibre, and not original G3/G4 closure.

## Actual source and exact arithmetic

Fix L=H/4>0. For integer m≥1 put N=12m², h=L/(N−1/2), r=L/N and a=h/(6m). Let s+=r+a, s−=r−a and

    K_m=(S_(s+) S_(s−))^(N/2).

S_s is the ORIGINAL strict fair reference with first ordinary duration s, fair arm log(2exp(s)−1), and final ordinary duration 2s−log(2−exp(−s)). These are positive for s>0; s−>0 since r/h=1−1/(2N)>1/(6m). Both clocks add exactly: each pair contributes COMMON4(s++s−)=8r and I-pair3(s++s−)=6r. Thus the full word has COMMON H and I-pair3L, while L/h=N−1/2 stays half an integer. The cell count is exactly N; chronological alternation is literal, not an unordered source mixture.

When H=log(2)/M with positive integer M, all s±,r,h are rational multiples of log2. Therefore t_s=exp(−s) and the original arm/bookend survivals t_s/(2−t_s),t_s²(2−t_s) are positive algebraic numbers; the fair coin is1/2. This does not assert the logarithmic durations themselves are algebraic. Adjacent ordinary bookends may be merged into positive ordinary factors without changing either action.

The exact identities are

    r/h=1−1/(2N),  a²/h²=1/(3N),
    r²+3a²=h²+h²/(4N²).

In particular a=O_H(h^(3/2)), r−h=O_H(h²), and N=O_H(h^(−1)).

## Full operator expansion and moment matching

Use the SAME fixed closed labelled-forest carrier and row convention. The public accepted fair third-jet proof supplies analyticity near0 and

    F(s):=log S_s=3sQ+s³A+s4B+O(s5), A=−R/3.

There is no s² term. The logarithm is its analytic branch nearI; the bound is fixed-carrier uniform for all sufficiently small positive s. No claim is made that A,B or F(s)/s are physical generators.

Let C(h)=F(h)/h. Then

    F(s+)+F(s−)−2r C(h)
      =2r(r²+3a²−h²)A
         +2(r4+6r²a²+a4−rh³)B+O_H(h5)
      =O_H(h5).

The cubic difference is exactly rh²/(2N²)=O_H(h5). For the quartic difference, r4−rh³=r(r−h)(r²+rh+h²)=O_H(h5), r²a²=O_H(h5), and a4=O_H(h6). The fifth-order remainders contribute O_H(h5), including 2r times the O(h4) remainder of C(h). Thus no uncancelled O(h4) symmetric pair term remains.

## Noncommuting pair and uniform logarithm error

Put X=F(s+), Y=F(s−). The linear-linear commutator vanishes. Its leading linear-cubic term is

    3(s+ s−³−s+³ s−)[Q,A]
       =−12ra(r²−a²)[Q,A]=O_H(h^(9/2)).

Linear-quartic terms are O_H(h5) even without using their improved antisymmetric cancellation; all remaining terms are smaller. Hence ||[X,Y]||=O_H(h^(9/2)).

For small fixed matrices X,Y, the bound

    ||log(exp X exp Y)−X−Y||≤C||[X,Y]||

is uniform in a fixed neighborhood of0. One need not assume commutativity or truncate BCH without a remainder: Duhamel's formula bounds exp X exp Y−exp(X+Y) by C||[X,Y]||, and the analytic log is Lipschitz nearI by its absolutely convergent power series. Equivalently, the convergent BCH remainder is a uniformly bounded sum of nested commutators containing [X,Y]. The constants depend on the fixed carrier/neighborhood, not m.

Consequently G=log(S_(s+)S_(s−)) satisfies

    G=2r C(h)+O_H(h^(9/2)).

Using the integer power directly avoids any claim about the principal logarithm of the long word:

    K_m=exp((N/2)G)=exp(L C(h)+E_m),
    ||E_m||=O_H(h^(7/2)).

A bounded-neighborhood exponential Duhamel estimate gives K_m−exp(L C(h))=O_H(h^(7/2)). Since exp(L C(h)) commutes EXACTLY with S_h=exp(hC(h)),

    [K_m,S_h]=[K_m−exp(L C(h)), S_h−I]
                =O_H(h^(9/2))=o_H(h4).

No multiplication of a per-cell error by an uncontrolled count is hidden: N/2=L/(2r) is explicitly used, and the final extra factorh comes from S_h−I.

## Exact consequence and limits

These are finite strict all-fair paired-clock words with phase distance1/2 and residual/h4→0. Therefore no generic inequality

    dist(L/h,Z)≤C_H[(||[W,S_h]||/h4)^alpha+h^kappa]

with fixed alpha,kappa>0 can hold uniformly for ALL such paired fair words. The canonical uniform reference-power family had Theta_H(h4); this alternating family changes its cubic moment and is not a contradiction to that earlier sharpness calculation.

This refutes only that generic critical-scale norm-to-phase premise. It does not prove any K_m exactly commutes, lies in the fairization image of an original EXACT commuting fitting tuple, matches a fixed target's complete finite panel, or violates a COMMON certificate. Exact-image stability and both original master obligations remain open. No coefficient bank, source engine, numerical experiment or compiler was run for this hand review.

Exact inherited public third-jet source: https://github.com/Sodelin/Research-Commons/blob/ba80d25ddd2d9ad6de54f5ea5835a315689f9a16/research/2026-10-31-g4-leading-prefix-channel/PROOF.md §2, SHA256 `0739a2669c7fd2f083a691736038f7eb6693c1f34a61d729b7baa98f251864c6`. Its fair physical specialization and original reference logarithm were independently source-checked in the public canonical-family packet at `a1f2c975aba06962eb614a9ab45519b4971b033b`, research/2026-10-31-canonical-fair-family-h4-sharpness.
