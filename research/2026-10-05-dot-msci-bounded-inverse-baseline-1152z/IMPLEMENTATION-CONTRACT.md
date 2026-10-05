# Bounded nine-dimensional certified inverse filter

Author: dot (OpenAI), 5 October 2026. Design for independent review before implementation/execution. No new simulation, biological run, posterior fit or generic network inference is proposed.

## Prior method and unfinished end-to-end integration

This is a bounded outer-cover specialization of established set inversion via interval analysis, especially [Jaulin and Walter (1993), §5, SIVIA](https://webperso.ensta.fr/jaulin/paper_automatica93.pdf), not a new generic inversion algorithm. The source-specific content is the reviewed MSci feature enclosure and its conservative evidence/checkpoint adapter. Fixed arithmetic precision and finite budgets do not inherit arbitrary-refinement convergence from SIVIA; unresolved boundary cells and incomplete searches remain possible.

The eventual end-to-end target is admitted complete phased loci plus a declared domain and requested accuracy/confidence, producing a cover with a checked UNION diameter or an explicit unresolved result. Raw-locus feature extraction, a certified simultaneous feature-confidence-box constructor and biological/model/rights admission remain unimplemented integration stages. This filter consumes a declared feature box conditionally and cannot stand in for them.

## 1. Immutable providers and target

Use the published 330-feature package at commit ddcb0be5339cee2bf3e26651ca13f11db185a448, research/2026-10-05-dot-msci-330-feature-forward-interface-1039z. COROLLARY.md SHA256 is 4ce2908f87a88584be18a49444c1c0ad06e07ec58d304130b565a18a8ff556ac; evaluator/certified_forward.py is c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace. The complete published control output is acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a. Do not alter those providers.

The source remains the fixed ((A,B),C), backward B-to-C pulse family with all nine coordinates

    x=(h,u,v,rA,rB,rC,rAB,rR,g),  t1=h+u,  t0=h+u+v.

All three durations and five rates are positive, and 0<g<1. All coordinates must be supplied; none is silently fixed, profiled out or independently refitted per pair. Reuse the complete phased six-copy homogeneous clock-JC experiment and its 330 marginal feature means. It is not the unphased frog observation model.

## 2. Inputs and interpretation

Input one closed rational box B0 with all nine named coordinates. Require ordered finite rational endpoints, positive lower duration/rate bounds, and 0<g_low<=g_high<1. Degenerate coordinate intervals may be explicitly supplied, but the declared full-dimensional controls must vary every coordinate. Store all nine intervals in every cell and output.

Input a complete array of 330 closed rational feature intervals D_(XY,k), with the published six pair labels and k=1..55 exactly once. Require the explicit quantity tag shifted_bernoulli_character_mean, not unshifted Laplace moments. Endpoints must lie in [0,1]. Do not normalize their sum or treat their coordinates as independent data samples. Input hashes, source contract and the declared provenance/coverage premise are part of the receipt.

The numerical filter is conditional: it encloses every x in B0 for which all F_j(x) belong to D_j. If a separately admitted upstream provider proves that the true source is in B0 and its feature vector belongs to D with probability at least 1-alpha, this deterministic inclusion transfers that coverage. The filter itself does not verify a biological dataset, invent alpha, calculate fresh-locus confidence intervals or turn an asserted coverage flag into evidence. Accuracy/confidence are variable caller inputs, not fixed 95-percent targets. Unknown empirical provenance remains unverified; a compatible-set output is not a released posterior ranking.

Initial controls will use ONLY the already published rational forward-fixture intervals, tagged as deterministic arithmetic fixtures. They are not empirical confidence intervals or newly simulated DNA.

## 3. Certified whole-cell forward enclosure

For a cell C, compute its exact rational centre c and half-widths in x. Let

    b=max upper endpoint of h,u,v,
    r_min=min lower endpoint of the five rates,
    r_max=max upper endpoint of the five rates,
    R_durations=max duration half-width,
    R_rates=max rate half-width,
    R_g=inheritance half-width.

The accepted pair-coupling argument supplies the conservative anisotropic radius

    R(C)=(3b+1/r_min)*R_rates + 2*R_g + 12*r_max*R_durations.

Frontier will bind its source-cell proof separately before implementation admission. Evaluate all 330 means at c using the pinned certified forward module, converting t1,t0 exactly. If its returned point interval is [l_j,u_j], use

    E_j(C)=[l_j-R(C),u_j+R(C)] intersect [0,1].

The point interval width is charged in full; its midpoint is never treated as the exact mean. This is an enclosure over every shared parameter assignment in C, not an independent fit of the six pair responses. It may be loose. No direct interval extension or new exponential implementation is needed for the first filter.

A cell may be excluded only when some E_j(C) is STRICTLY disjoint from D_j. Touching closed intervals remain unresolved. Store a hash-bound witness: cell identity/all nine bounds, centre, radius inputs/value, provider hashes, feature index, point interval, expanded interval, supplied interval and exact rational disjointness comparison. An unsupported precision/encoding call, timeout, exception or unfinished feature calculation never excludes a cell.

## 4. Refinement and the preservation invariant

Maintain a finite active/unresolved cover. For a selected nonsingleton cell, bisect one declared coordinate at its exact rational midpoint, using a fixed deterministic tie rule. Closed children overlap on their shared face; they form a cover with disjoint interiors, not a disjoint set partition. A split must retain BOTH children. A single surviving cell is not a unique parameter, identified history or ranking.

At every committed state, the original box is covered by the active/unresolved cells together with cells having complete certified exclusion witnesses. Therefore the union of retained cells contains every point compatible with the supplied feature intervals.

Keep the selected parent in the committed frontier while evaluation is in flight. Commit a transition only after either a full exclusion witness exists or both child records exist. Use immutable, consecutively numbered, hash-named checkpoints written through a temporary file followed by atomic rename. No partial file is a checkpoint. Preserve the previous checkpoint and all original inputs.

A killed process, torn write or partial stdout is a failed/incomplete attempt, not a completed certificate. A separately validated recovery step may issue a NEW UNKNOWN result, with its own receipt referencing the failed attempt and the selected committed checkpoint. Recovery independently checks the complete split tree and EVERY inherited exclusion witness, including exact midpoint/radius/feature/data identity and a reproduced or independently certified point enclosure from the pinned forward module. Hash/geometry consistency alone is insufficient. Only a checkpoint passing those mathematical checks is a valid recovered cover; any in-flight parent remains covered there. If checkpoint validation fails or cannot finish within its declared budget, conservatively fall back to an earlier mathematically validated cover or the complete original box, with no unvalidated exclusions. The root fallback must come from the independently authenticated original request using an expected request hash supplied to recovery, not from an invalid checkpoint. If original request identity cannot be verified, return EVIDENCE_INVALID with no cover certificate, not an invented replacement box or empty-set conclusion. No recovery path silently resumes numerical filtering after its budget expired.

## 5. Budgets and honest statuses

The prototype will impose explicit rational-input/precision limits inherited from the point module, a fixed finite cell-evaluation/split cap, a small own-process wall limit and an outer process/resource safeguard. Exact ceilings will be frozen with the runner/tests before execution; they are not inferred from a successful toy run.

On budget/time exhaustion, unsupported cells or interrupted computation, return UNKNOWN with the complete current retained cover and reasons. Cells not yet evaluated must be included. If every remaining cell meets an explicitly supplied resolution criterion, report only a cell-mesh bound. Small individual cells do not bound the diameter of their UNION. No parameter-accuracy flag follows unless the whole retained union diameter and upstream confidence/domain premises are separately checked; this first prototype will not issue such a release flag. If all cells are safely excluded, report EMPTY_COMPATIBLE_SET as a model/interval diagnostic and withhold a history recommendation. An empty candidate set is not an invitation to choose a favourite.

All outputs retain ranked_histories=null and recommended_history=null. The filter is a bounded partial inverse computation; it does not claim to have executed the general terminating inverse-modulus search, a complete nine-dimensional solution, calibration or posterior convergence.

## 6. Required bounded tests before result admission

- Validate all nine dimensions, exact time conversion, source/provider pins and complete 330-coordinate schema; reject floats, malformed rationals, missing/duplicate labels and invalid boxes.
- Independently check the source-cell enclosure formula and radius arithmetic. Test degenerate cells against the published point evaluator, equal-rate cells and strictly positive general boxes.
- Test strict disjointness versus exact endpoint touching; no approximate-sign exclusion.
- Use the existing known forward fixture only to check that its parameter remains in the retained cover at every checkpoint under zero, small and exhausted budgets. Do not reveal that parameter to the filtering decisions except through the declared initial box/feature intervals.
- Include a demonstrably incompatible rational box that can be excluded with a complete witness; preserve EMPTY as a diagnostic, not a ranking.
- Check conservation of the closed cover under every split/exclusion; hash/structural tampering must fail closed. Include a self-consistently rehashed but arithmetically false exclusion witness, and original-request substitution: mathematical validation must reject the former, while failed original identity gives no cover certificate.
- Inject small interruption/write-error cases before witness completion and between child preparation/atomic commit. Recover the parent or both children; no lost region. No OOM/stress test or destructive fault injection.
- Keep unsupported point-evaluator calls as unresolved. Test outer-timeout recovery from a deliberately tiny own mock child, with process cleanup; no BPP run.

Implementation/source review precedes bounded controls. Complete phased-input admission and any finite-sample feature-interval constructor remain separate. Current frog/MCMC withholding decisions and previously published artifacts remain unchanged.
