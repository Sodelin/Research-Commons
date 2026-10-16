# Strength and directed prior-work check for the finite-pair certificate

Date: 2026-10-16, 23:39 UTC. Author: dot, working with Nolan.

## Recommendation

Present this as a **reproducible, exact-arithmetic finite example within a declared model**, supplementing the earlier independently reviewed asymptotic theorem. Do not present it as a new physical principle, a demonstration of protected Majorana modes, or a verified counterexample inside the original Taylor implementation. The mathematical value is the auditable finite parameter and error budget: 1 eV end onsite, fixed rational hopping, opposite reflection-determinant margins, and a common energy-report tolerance of 0.049995 μeV.

## Prior sources inspected for this check

1. [Araya Day, Manesco, Wimmer and Akhmerov, Identifying biases of the Majorana scattering invariant](https://arxiv.org/html/2504.01069v1), especially Sections 2, 3.1 and 4. The established lead-bias mechanism compares the splitting with lead-induced widths; Section 3.1 gives det(r) = (E_M² − Γ_L Γ_R)/(E_M² + Γ_L Γ_R), and tests tunnel-barrier bias in a microscopic wire. Thus neither lead dependence nor the possibility of misleading finite-system labels is new here. Their analysis also makes clear why reflection-determinant sign and thermodynamic/topologically protected Majorana behavior must not be conflated. Our finite certificate keeps the external leads fixed while changing internal onsite potentials, and directly checks the full 60-site scattering problem. That distinction describes this construction; it does not establish historical novelty.

2. [Das Sarma, Sau and Stanescu, Spectral properties, topological patches, and effective phase diagrams of finite disordered Majorana nanowires](https://arxiv.org/html/2305.07007), Section V.1 and discussion. This source explicitly separates negative reflection determinant from well-isolated end Majorana modes in a finite disordered wire. It supplies prior context for the target-definition caution; it does not by itself authenticate our exact finite pair or Taylor's implementation.

3. The spectral perturbation inequality and overlapping bounded-error balls are classical mathematics. The present work uses them rather than claiming to discover them. The interval kernel and block Schur-complement method are verification machinery, not new physical laws.

## Directed search coverage and limits

A bounded search on October 16 used the phrases “topological visibility energy spectrum leads,” “fixed lead coupling nearly identical energy spectra topology disorder inverse problem,” and the exact lead-bias paper identifier. It recovered the sources above and adjacent transport/disorder work. No exact published match to this particular rational 60-site certificate was established in that pass. This negative search result is not proof of novelty; no exhaustive citation graph, all-version code comparison, or specialist priority review was completed.

One search result also pointed to an older public dissertation/code collection. It is not authenticated as the original Taylor implementation and was not substituted for it. No previously inaccessible original-model route was retried, and no author was contacted.

## Exact remaining boundaries

- The finite certificate is for one rational hopping; the prior asymptotic result has the wider hopping interval.
- The all-field energy bound is a common-parameter worst-case bound. It is not an empirical estimate of instrument performance or classifier error frequency.
- The explicit pair need not have identical energy curves. A sufficiently precise noiseless calculation might distinguish it.
- The barrier is physically extreme for the stated effective model. Feasibility and effective-model validity are unestablished.
- Positive internal dissipation, bounded-disorder restrictions and additional calibrated measurements require their own analysis.
- Original Taylor lead/disorder implementation admission and the short-wire variant exclusion remain as recorded in the accepted packet.

These limits are reasons for careful framing, not mathematical defects in the explicitly declared finite model. Independent certificate and proof review is still required before accepted-result publication.
