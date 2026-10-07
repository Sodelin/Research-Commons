# A C-rate component feeding the original g bound

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **Hand-derived component; independent review pending.** No arithmetic job, provider evaluation, observation replay, sampling, inverse run or compiler was performed for this note.

This addresses the rC error in the [upstream g inequality](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md). It uses the same original nine shifted means, domain D, rate ties and source. It does not supply the missing h or A=h+u recovery, a full confidence difference set, or whole-domain width success.

Put z=8/3, c=rC, R=rR and T=h+u+v in [3/32,3/8]. Original c,R lie in [1/2,6]. Define `q(r)=r/(r+z)` and `H(r,t)=q(r)*(1−exp(−(r+z)t))`. The original [pair formula](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, gives, for RAW AC1 moment C and CC1 moment Q,

    C=exp(−zT)*q(R),
    Q=H(c,T)+exp(−cT)*C,
    mu_CC=(1+Q)/2,  mu_AC=(1+C)/2.

This retains the shared root contribution through the observed AC1 mean rather than separately propagating root-rate error. Expectations belong to coherent original sources; no independently assigned empirical moments are treated as a source.

At fixed original T,R, the same continuation derivative used in the [accepted AA1 component](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md) yields

    partial_c mu_CC
      =(1/2)*[z*integral_0^T t*exp(−(c+z)t)dt
               + T*(1−q(R))*exp(−(c+z)T)]
      ≥ (3/169)*(1−exp(−13/16)) =: alpha_C.

The analytic minimum is attained at c=R=6 and h=u=v=1/32. The derivation uses c+z≤26/3, 1−q(R)≥4/13, and T≥3/32 exactly as in AA1. For x=13/16, `exp(x)>1+x` gives

    alpha_C > (3/169)*x/(1+x) = 3/377.

This strengthens the [previous shifted derivative bound](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/TRIANGULAR-BLOCK-LOWER-BOUNDS.md) 1/512. The reciprocal component constant is now 377/3, with no new exponential evaluation or transcendental equality test.

For ANY two original sources, use subscript 0/1 and Delta=value0−value1. Swap only c0 for c1 in source0. This remains in original Cartesian D and leaves T0 and AC1 unchanged. The source derivative bound applies throughout that rate segment. At the fixed rate c1, the exact algebraic nuisance comparison is

    [(1+H(c1,T0)+exp(−c1*T0)*C0)/2]
      −[(1+H(c1,T1)+exp(−c1*T1)*C1)/2]
      = exp(−c1*T0)*Delta mu_AC
        +(c1/2)*integral_(T1)^(T0)
               exp(−c1*t)*(exp(−z*t)−C1)dt.

No source-only derivative bound is applied to a mixed (T,C1) nuisance path. Define m=min(T0,T1) and

    L_T=(c1/2)*exp(−c1*m)
        *max(|exp(−z*T0)−C1|, |exp(−z*T1)−C1|).

The rate swap, triangle inequality and monotonic exponential endpoint bound give

    |Delta rC| ≤ alpha_C^(-1)*[
       |Delta mu_CC|+exp(−c1*T0)*|Delta mu_AC|
       +L_T*|Delta T|].                          (1)

Both C1 and exp(−zt) on that integral interval lie in [0,exp(−z*3/32)]. Also `c*exp(−c*3/32)` increases on c in [1/2,6], because c*3/32≤9/16<1. Hence

    L_T ≤ 3*exp(−13/16) <48/29,
    |Delta rC| ≤ (377/3)*[
       |Delta mu_CC|+|Delta mu_AC|+(48/29)*|Delta T|]. (2)

Normalized rC error uses original rate width 11/2 and is at most 2/11 times (1) or (2). Sourcewise coefficients in (1) should be retained when rigorously enclosed; the uniform version is a fallback, not a numerical precision claim.

The new component feeds rC into the SAME g/AA1 dependency chain and exposes root-time error as the remaining upstream term. Original AC1/AC2 recovery must still control T. The harder h/g ratio and A/onset profile require cross-nuisance bounds on their entire valid comparison ranges; pointwise nonzero determinants do not supply them. Original mean-error admission, all source cells including between-cell pairs, and complete exported union widths remain separate. No cell was evaluated, narrowed or dropped, and no retrospective confidence is issued.
