# A refined all-source COMMON representative bound

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026. **Hand candidate for independent review.** This substitutes the accepted positive second-order generator reconstruction into the old accepted G6 chain/calendar argument. It proves a new conservative count bound under the same source/observation contract, not a new G6 characterization or formal endpoint.

## 1. Keep the inherited proof through compressed generators

Use [G6 Appendix A.2](../2026-10-01-g6-effective-certification/PROOF.md), with the exact separate COMMON source semantics and arbitrary entering forests. For M≥2 and 0<η<1, its constants are

    C=binom(M,2),   d=M−1,
    W=1+ceil(log₂(6C/η)),
    δ=min(1/2,η/(6C²W)),
    h=min(1/2,η/(3R_M W)),
    U₀=W/h,

where R_M≥1 is the old computable rational pure-death coefficient constant. No new estimate for R_M is introduced.

Clipping keeps a prefix with loss sum at most W and costs at most η/6. Keep its strong bare factors q>δ: there are at most ceil(W/δ). Poissonizing weak factors costs at most η/6. The exact generator compression leaves at most d positive atoms. Replacing atoms within h of survival one by their ordinary-drift limit costs at most η/6. The remaining exponential generator has total intensity U≤U₀ and s≤d atoms with strictly interior survival ratios. All ordinary drift is added to the same retained positive deterministic baseline.

Every one of these statements and its proof is inherited. The same baseline remains in (0,1), and all bare strong factor probabilities/ratios stay strict. No original source-size or parameter floor is used.

## 2. Replace only the last Euler reconstruction

Instead of the old first-order Euler cells, set

    L₀=ceil(max(1,U₀,sqrt(3U₀³/η))).

For a nonempty residual generator, use the accepted second-order count construction with L=L₀ and N_j=ceil(L₀u_j/U). Because L₀≥U₀≥U and L₀²≥3U₀³/η,

    reconstruction TV error
       ≤U³/(2L₀²)≤U₀³/(2L₀²)≤η/6,

and there are at most 2(L₀+s)≤2(L₀+d) new strict bare factors. Empty residual generators need none. Combining with retained strong factors yields the uniform bound

    B_com,2(M,η)
       =ceil(W/δ)+2d+2ceil(max(1,U₀,sqrt(3U₀³/η))).      (B2)

Allocate the ONE positive deterministic baseline across every strong and newly constructed bare factor by the [contextual positive-source construction](CONTEXTUAL-POSITIVE-SOURCE-BRIDGE.md), §3. This realizes the aggregate by at most B_com,2 actual positive bigons, with positive arms, connectors and leading ordinary population. It does not realize identity arms as physical gadgets. Grouping is licensed only for these unexposed COMMON factors, since their Kingman operators commute and their natural site bits are independent.

The inherited clipping, Poissonization, near-one replacement and the new reconstruction consume at most 4η/6. Any old separately budgeted connector repair consumes at most η/6; the exact aggregate baseline allocation itself adds zero kernel error. Therefore total full-forest TV error is at most η. Numerical implementation rounding would need its own remaining budget and is not executed here.

This proves the old COMMON positive-chain approximation conclusion with B_com,2 substituted for B_com. INDEPENDENT approximation retains its original chronological bound; no mode transfer occurs.

## 3. Same-endpoint finite calendar and retained-bank representative

Use the old cut guards, root-retained source core and direct switching-target preservation. Retiming each constructed run at its original endpoints is exactly the source bridge's §4, with freely variable positive edge-specific constant rates. Previously formed subtrees/bin histories and original crossing populations remain intact. One replacement source handles all natural profile allocations/rows; optional marked controls retain their old unchanged-run contract.

Thus in the original planar class and the accepted RAW NONPLANAR extension, for n≥4, J cuts and 0<ε<1, the natural COMMON representative bound becomes

    R_com,2(n,M,J,ε)
      =r₀+E₀[2J+(2J+1)B_com,2(M,ε/[E₀(2J+1)])],
    r₀=2n−2, E₀=8n−8.                               (R2)

The same-target actual source has joint finite-profile TV error at most ε. This is an existence/construction theorem for every finite original source, independent of its original level/blob/serial-word count. The original source is not claimed to satisfy R2, and full metric-TV laws are not claimed to have this representative bound.

For the accepted finite original-ID marked-control extension, put K=K_h+2K_e for the union of marks, and T=E₀(2J+1)+K. Its source bound is similarly

    R_control,com,2
      =r₀+2JE₀+K+T B_com,2(M,ε/T).                 (RC2)

The original marked primitives keep their actual IDs and transformations. This formula requires the supplied finite mark bound and unchanged private runs. It does not cover an unrestricted control registry or a bank that changes newly inserted private hybrid operations.

Equations R2/RC2 are direct substitutions into the [accepted nonplanar source proof](../2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md), §§2–3. No new graph counting argument, target decoder or clock-feasibility relaxation is used.

## 4. Quantitative interpretation and exact limits

At fixed M as η→0, W=O(log(1/η)), δ is proportional to η/W and U₀ is proportional to W²/η. Formula B2 is therefore

    O(η⁻² log³(1/η)),

whereas the old displayed first-order reconstruction bound was O(η⁻³ log⁴(1/η)). This compares two conservative uniform construction bounds, not an optimal all-source rate or a demonstrated runtime improvement. The separately accepted Θ(ξ⁻¹ᐟ²) lower/upper statement concerns one FIXED compressed Poisson family; U₀ grows here with η, so its fixed-intensity exponent cannot be substituted without charging that dependence.

All new second-order reconstruction/count and physical allocation steps have exact symbolic statements. No cutoff, graph catalogue, age/rate cell, source witness, finite-calendar compiler, numerical error or resource timing was executed for B2/R2/RC2. The displayed formulas are mathematically computable bounds; they are not an implemented global solver or a Lean proof.

Exact source membership and input-effective exact witnesses remain the original G3 open problem. Connected timed-bin/actual-source formalization and the other effective/statistical G6 consumers remain separately open in the Cloud formal assembly.
