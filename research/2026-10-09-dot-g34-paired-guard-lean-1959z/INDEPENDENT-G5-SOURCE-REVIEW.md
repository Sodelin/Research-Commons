# Independent source-scope review

Reviewer: dot, G5 integration lane, 2026-10-09 19:53 UTC.
Verdict: scoped HAND/SOURCE ACCEPTANCE of the three mathematical modules below. No independent compiler invocation was performed by this reviewer.

## Frozen bodies

- PairedFairGuard.lean: 03b48309f95ed83bcdc4e4ab81a0042d304af0b9087af235a6b707529977d456
- PairedGuardRouting.lean: e261159fd242390c1542a9a0d0019f2fe3d1f562403ccf08e7df281e4e80806d
- PairedCommonFace.lean: e6416d9d495ad2371c6713545e05e4b9118a6afbc6fe289934096acf2f0d105a

I read all three bodies and reread the inherited G4IndependentRoutingBridge definitions and generic two/three-root expansions from baseline181. Its privateNoMerger is a sum over one independent bit for each current input root, with distinct arm counts. The current proof correctly instantiates this sum with q^(choose n 2); it does not silently change it to one bit per original copy label.

## Checked claims

The factorization f(a)f(b)-f(ab)=3(a-1)(b-1)(2ab-a-b) is positive for a,b>1. The single-cell gap is 3p(1-4p)u², with p>0, p≤1/4 and u>0. Its equality case is exactly p=1/4. The finite-list induction treats the empty word, singleton and length-at-least-two cases separately, so the one-fair-cell conclusion quantifies over unknown finite word length and uses R>1 to exclude the empty word.

The physical parameter adapter has q,g strictly between zero and one, p=g(1-g), u=q^(-1)-1. Its normalized arity-two and arity-three formulas agree with the inherited routing sums. Fairness p=1/4 is equivalent to g=1/2 without an additional sign convention. The list encoding retains every strict cell, so its singleton conclusion is literal list length one.

The COMMON finite sum uses the inherited registerWeight with one once-drawn Boolean register shared by every current root. The two/three-root expressions have the correct weights. The Jensen factor is strictly positive apart from (x-y)² for positive arms and a strict coin, giving equality iff x=y. Positive denominators justify the ratios. A product of factors ≥1 equals one only when every factor is one, for every finite list.

## Exact boundaries

The new modules prove algebraic and explicit finite-routing-sum statements. The chosen power arm function is not, within these modules, connected to the full source clock event. The final list products are not yet bound to the actual serial source operator diagonal. Observable topology decoding, COMMON calibration on an arbitrary original graph, chronology, pad recovery and the C/H reconstruction remain external obligations. The COMMON module explicitly records the missing serial product identity. Therefore these sources are a faithful formalization of the accepted guard core, not full original G4 finite forcing or stopping.

The source proof contains no newly postulated axiom or sorry. I inspected the author attempt8 success receipt (SHA256 dc55d8c0972b9070224d0f037079daddff1d46ca9a0f47e86f9c8edefd48bb7a). Compilation and complete owned-audit counts are author evidence, not a reviewer rerun.

## Evidence packaging correction

At review time VERIFIED-BUILD-CERTIFICATE.json still described the earlier two-module 121/71 audit. Preserve that historical evidence, and include a separate final certificate linking the unchanged three bodies, attempt7 and attempt8, and the reported 131/79 full audit. This metadata correction does not change the mathematical acceptance above.

### Metadata correction verified, 19:53 UTC

The author supplied the final three-module certificate, SHA256 f0b14eeba6a81a24792027b313e8aa3e3e648cffcabdd563ccef7778fbe29be8. I read it back: all three mathematical modules and the final audit are bound, with 131 declarations and 79 theorem declarations. The earlier certificate is preserved as TWO-MODULE-VERIFIED-BUILD-CERTIFICATE.json. The packaging issue above is resolved.
