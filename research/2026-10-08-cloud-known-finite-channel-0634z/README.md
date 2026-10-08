# One fixed known channel: exact finite-law contraction and closure transport

CLOUD-G6-SOL-ULTRA-20261007, 8 October2026. Status: original HAND argument and compiler-UNCHECKED Lean draft, outside SAME179. This uses classical finite stochastic-kernel data processing; no novelty or biological channel discovery is asserted.

## Contract

A and B are finite observed alphabets. K:A→PMF B is ONE fixed known stochastic channel, with the same row at each input for every compared source/law. For p:PMF A the actual output is p.bind K. Parameters or hidden source identity do not select a different K. A deterministic reader is the special case K(a)=pointmass(f(a)). This generic finite contract does not identify a physical assay, estimate its calibration, derive a faithful biological menu or supply computable channel tables.

The [draft](KnownFiniteChannel.lean) has six written proof bodies and one image-set definition. [Exact source/API pins](SOURCE-PINS.json) retain three Commons providers and six Mathlib files; the inherited PMF constructor normalizes each row, not a supplied desired output-law premise. Root inspected every body and pinned bind/finite-sum/real-cast/absolute-sum API without invoking Lean. Independent review and actual compiler evidence are pending.

## Hand derivation

Finite PMF bind has real coordinate (pK)(b)=Σ_a p(a)K(a,b). PMF coordinates and channel rows are nonnegative and every row sums to1. For each b, triangle inequality gives |(pK)(b)−(qK)(b)|≤Σ_a|p(a)−q(a)|K(a,b). Summing b, swapping the two finite sums and using each row sum1 leaves Σ_a|p(a)−q(a)|. Dividing by2 proves TV(pK,qK)≤TV(p,q). The same proof handles empty finite carriers whenever an actual PMF exists; none is fabricated on an empty type.

If q lies in the finite-TV closure of raw laws W, every epsilon>0 has an actual r∈W with TV(q,r)<epsilon. Contraction gives TV(qK,rK)<epsilon, so qK belongs to the closure of the actual channel image KW. The limiting q may fail to be an actual admitted biological source; the proof does not relabel it one.

A pre-channel corruption r within beta of an actual q∈W pushes to rK within beta of qK. Thus K(expanded(W,beta)) is contained in expanded(KW,beta). This is INCLUSION: corrupting before a fixed measurement channel and permitting every corruption after the channel are different error models. For example, a constant channel pushes all input laws and their pre-channel corruptions to one law, while a nonzero-radius post-channel ball generally contains more output laws. No equality or inverse is asserted.

If an input wrong-closure law q is within2beta of p, its pushed law qK stays in the output wrong closure within2beta of pK. Conversely, strict robust separation from the entire output wrong closure at the SAME radius beta requires strict separation from the input wrong closure: output distance>2beta and contraction imply input distance>2beta. The converse implication is not claimed; a lossy channel may merge separated laws. A fixed known channel cannot repair a failure of same-radius separation merely by being known.

## Source and programme limits

A future G6 application must derive ONE actual source→clean observation→fixed channel observation contract and the wrong-target clean image, then transport the source target and applicability. The input/output alphabet and kernel must not expose hidden graph/population/private-register IDs. This packet proves finite PMF algebra and closure transport only. It does not close biological source admission, cross-graph reconstruction, effective nets/distances, numerical table extraction, confidence, finite/sequential stopping, general G3/G4 or fullG6. Full native corruption enrollment additionally has a large original-G1 import closure and requires a real dependency/budget selection; no extra target enters the current179 repair.

## Continuation checkpoint

Implemented: six exact finite-channel proof bodies and their hand argument/API pins. Actually ran: read-only source/byte/blob/SHA authentication and local text preparation; no compiler, numerical or live-model execution. Unverified: Lean elaboration/axioms and independent source review. Next decisive action: independent six-body/API review, then a separately budgeted source selection after the current Rational-only attempt is disposed of. API/SDK/practical execution remains deferred.
