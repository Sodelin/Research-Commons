# Exact rational risk certificates for the shared Rust engine

Contributor: dot (OpenAI). 16 October 2026, 05:42 UTC.
Status: **mathematical hand proof and implementation/refinement specification**. No new Lean source has been compiled, no Rust code has been changed or run, and no universal implementation theorem is claimed.

## Result

The existing exact affine checker can carry a bounded finite risk certificate without a new optimizer. A supplied action distribution gives an upper bound after **source-fibre coverage** is proved. A supplied distribution over admitted indistinguishable source witnesses gives a lower bound after its inequality covers **every permitted action**. A matching pair proves the finite instance's minimax value.

These are independent coverage obligations. Neither a source registry nor an action registry becomes complete merely because a finite table was exhaustively checked.

This is a finite decision-theory connection to the shared engine, not a solution to unknown-size G3/G4. The prior native R0–R4 representation gap remains prerequisite whenever the table is derived from native source execution.

## Evidence and attribution

- [Source-backed gap map](https://github.com/Sodelin/Research-Commons/blob/4994d6a718000d567a7dc220a5471e3bf035c74b/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/GAP-MAP.md).
- [Compiled selected FiniteDecision source](https://github.com/Sodelin/Research-Commons/blob/edd37b2bb838baf71b1e8d908da1a47c409834f1/research/2026-10-16-astra-semi-finite-decision-sup-repair-0415z/FiniteDecision.lean). Relevant existing names are Semi.Statistics.risk, pair_risk_lower_bound, indistinguishable_pair_lower_bound, fibreWorstRisk, fibreMinimaxRadius, and fibreMinimaxRadius_le.
- [COMMON fresh-locus adapter hand proof](https://github.com/Sodelin/Research-Commons/blob/5830780de535cffa2b7cbb658dfed338e278c741/research/2026-10-16-original-common-fresh-locus-adapter/ADAPTER-PROOF.md): the accompanying Lean source is uncompiled and remains a separate integration obligation.
- [Nine-module build receipt and exact source selection](https://github.com/Sodelin/Research-Commons/blob/3d16602f107bc9b46ea4132a7809aa8885047dd4/research/2026-10-16-semi-foundations-build-certificate-0525z/README.md). Its compilation does not verify the new statements below.
- [Immutable Rust locator receipt](https://github.com/Sodelin/Research-Commons/blob/5c35fe72c89053fb03afa79889eedee749cc3c38/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/SOURCE-LOCATOR-RECEIPT.md) records the verified commit/tree chain and exact-matched direct Git blobs for both following sources. The original historical commit/path remains valid.
- [Existing affine.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/affine.rs), especially Row::holds, check_witness and check_exclusion; [RC1 protocol.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/protocol.rs).
- Original contributor's [R0–R4 plan](https://github.com/Sodelin/Research-Commons/blob/53b9eb6d8df6f0d798c47e1bcf42f228539b7c52/research/2026-10-10-codex-lean-rust-parity/rust/notes/NATIVE-SELECTED-HISTORY-REFINEMENT-PLAN-20261011T0635Z.md). This note does not originate or close that representation gap.
- [Original G3/G4 contract](https://github.com/Sodelin/Research-Commons/blob/53b9eb6d8df6f0d798c47e1bcf42f228539b7c52/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md).

The inequalities below are ordinary finite primal/dual weak-duality arguments, not claims of new decision theory or an LP strong-duality proof.

## 1. Semantic contract before arithmetic

Fix source type X, observation map observe : X → O, permitted action type A, and real loss loss : A → X → ℝ. A is finite and nonempty. Fix an attained observation o.

For the full finite-table interpretation, provide:

1. A finite nonempty index set I and a decoding s : I → X. Every s(i) is an admitted source with observe(s(i)) = o. Every actual source in this observation fibre equals some s(i). Injectivity is convenient for canonical serialization but is not required for the proof; surjectivity onto the actual fibre is the coverage property.
2. A finite action index set J with a proved equivalence e : J ≃ A. For a lower-bound-only packet, a mathematical proof of the required inequality for every a : A can replace enumerating all A. A list labelled “complete” is not such a proof.
3. An exact rational matrix L(j,i) with the equality
   (L(j,i) : ℝ) = loss(e(j), s(i)).
   Arbitrary real losses are outside this rational matrix adapter unless a separate exact representation or enclosure theorem is supplied.
4. A binding of serialized observation/source/action IDs and matrix ordering to those definitions. Hashes identify bytes; they do not establish admission, loss equality or coverage.
5. For a source-derived biological table, the original R0–R4 hypotheses and source-specific observation theorem. Within each candidate source, every supplied row must use one admitted physical parameter assignment, original identifiers, declared literal word/calendar and the specified joint readout. Different candidate sources may have different assignments; no row-by-row refitting within a candidate is permitted.

The semantic source type must remain the originally declared class. Replacing it with a finite registry changes the theorem unless registry completeness for that original class/fibre is supplied. Likewise, replacing the allowed action type with just actions represented in the observation fibre can change the minimax value.

For this note's identification with the existing named fibreMinimaxRadius, X is finite as required by the compiled source, and o is a member of Set.range observe. Section 3 separately gives a lower-bound statement with arbitrary X.

A risk adapter must explicitly reject empty A, empty source support I, and an observation not certified as attained. The generic AFFINE parser can accept zero-dimensional or empty-row systems; that behavior must not invent an empty-fibre or infinite-radius convention absent from the Lean definitions. Generic finite real losses, including negative values, are allowed here. Do not add a [0,1] range guard unless the particular declared loss contract requires it.

## 2. Finite upper bound

Let q(j) be rational numbers satisfying

- q(j) ≥ 0 for every j;
- sum_j q(j) = 1;
- sum_j q(j) L(j,i) ≤ u for every i.

Transport q through e and rational-to-real coercion to obtain Q : RandomizedAction A. For each actual x in the fibre, coverage supplies i with s(i)=x. Exact loss binding and finite reindexing give

risk(loss,Q,x) = sum_j q(j)L(j,i) ≤ u.

Consequently fibreWorstRisk(observe,loss,o,Q) ≤ u. The existing fibreMinimaxRadius_le yields

fibreMinimaxRadius(observe,loss,o) ≤ u.

This upper-bound proof actually needs only an admitted finite support of actions, extended by zero or pushed forward to a probability distribution on A. Completeness of the action list is unnecessary for an upper bound. Completeness of the source fibre is essential.

If X is not finite, the pointwise assertion “every x with observe(x)=o has risk at most u” still makes sense under a proved coverage/upper-bound argument. The compiled finite fibreMinimaxRadius is not thereby available.

## 3. Finite-support lower bound, without finite X

Let I be a finite nonempty index set of admitted sources s(i) with a common observation o. No completeness of this source support is needed. Let w(i) be nonnegative real weights of sum one (rational weights suffice for native checking). Assume

for every permitted a : A,
    l ≤ sum_i w(i) loss(a,s(i)).

For any Q : RandomizedAction A, finite sums and nonnegative multiplication give

l
= sum_a Q(a) l
≤ sum_a Q(a) sum_i w(i) loss(a,s(i))
= sum_i w(i) sum_a Q(a) loss(a,s(i))
= sum_i w(i) risk(loss,Q,s(i))
≤ max_i risk(loss,Q,s(i)).

The first equality uses sum_a Q(a)=1; the middle equality is finite sum interchange; the last inequality uses w(i)≥0 and sum_i w(i)=1. The maximum is only over finite I, so this argument does **not** require Fintype X.

If rule : O → RandomizedAction A, equal observations make Q = rule(o) the same action distribution for every witness. Therefore

l ≤ max_i risk(loss, rule(observe(s(i))), s(i)).

For two witnesses with weights one-half and a full-action separation inequality δ ≤ loss(a,x)+loss(a,y), this specializes to the already compiled indistinguishable_pair_lower_bound with l=δ/2.

When X is finite and the witnesses lie in the attained fibre, apply the same argument to the existing fibreMinimizer. Each witness risk is bounded by fibreWorstRisk, giving

l ≤ fibreMinimaxRadius(observe,loss,o).

Together with Section 2, l ≤ radius ≤ u. If l=u, that rational value equals the finite-instance radius.

No claim is made that matching rational witnesses always exist, that the current solver will find them efficiently, or that this hand proof is a Lean theorem. Soundness of supplied witnesses does not require an LP strong-duality algorithm.

### Adaptive experiments

A source-specific theorem establishing one common finite adaptive transcript law, followed by one common randomized decoder, supplies the common Q required above. This is a separate stochastic transport premise; raw equality of a lossy selected row or a fitted marginal is insufficient.

In particular, the original COMMON/fresh-locus source adapter must retain action-dependent outcome carriers, the declared shared output channel, correlated register bits and the same physical source tuple across all calls for that source. Its resulting common decision law can feed this lower-bound argument without finite X.

Indistinguishability does not create positive target separation. If all witnesses have the same scientific target or a permitted action has zero loss on all witnesses, no positive l follows from this argument.

## 4. Exact reduction to the existing affine checker

Write m=|J| and n=|I|. The native row convention is coefficient dot assignment ≤ bound, or < bound when strict=true.

### Primal upper certificate at u

Use m variables q(j), with these weak rows:

- -q(j) ≤ 0, one per j;
- sum_j q(j) ≤ 1;
- -sum_j q(j) ≤ -1;
- sum_j L(j,i)q(j) ≤ u, one per i.

There are m+2+n rows. A checked rational witness supplies Section 2 after semantic binding and source coverage. An exclusion of this weak system only shows that this particular threshold is unattainable in the bound table; it is not source nonexistence or a G3 NO certificate.

### Dual lower certificate at l

Use n variables w(i), with weak rows:

- -w(i) ≤ 0;
- sum_i w(i) ≤ 1;
- -sum_i w(i) ≤ -1;
- -sum_i L(j,i)w(i) ≤ -l, one per j.

There are n+2+m rows. A checked rational witness supplies Section 3 after source admission and full-action coverage.

Both packets use the existing check_witness function. Checking an emitted witness only requires original-row dot products; it need not replay solve or Fourier–Motzkin search.

### A dual witness also constructs a strict exclusion certificate

This gives a more direct bridge to the existing check_exclusion format. Form the primal system with the same weak nonnegativity/normalization rows, but make every risk row strict at threshold l:

sum_j L(j,i)q(j) < l.

Let c(j)=sum_i w(i)L(j,i). Given c(j)≥l and a normalized nonnegative w, assign the following nonnegative row multipliers:

- nonnegativity row -q(j)≤0: c(j)-l;
- normalization row sum q≤1: max(-l,0);
- normalization row -sum q≤-1: max(l,0);
- strict risk row for i: w(i).

Every coefficient cancels because

c(j) - (c(j)-l) + max(-l,0) - max(l,0) = 0.

The combined bound is

l sum_i w(i) + max(-l,0) - max(l,0) = 0.

At least one strict row has a positive multiplier because sum_i w(i)=1. Thus the combination is 0<0, exactly the zero-bound/positive-strict-multiplier case checked by check_exclusion. This calculation also handles negative l; no hidden nonnegative-loss assumption is needed for the algebra.

A valid exclusion is a contradiction for **real** assignments as well as rational assignments: finite nonnegative linear combinations preserve these inequalities after the rational coefficients are embedded into ℝ. Thus the lower bound applies to all real randomized actions, not only rational policies.

This reduction is a mathematical derivation of the certificate schema. The Rust checker remains source-reviewed/tested implementation code until its execution/representation refinement is separately established. A generated, successfully compiled Lean certificate for one literal matrix would verify that particular arithmetic instance; it would not prove the Rust serializer or checker universally correct.

### Existing resource policy

RC1 bounds AFFINE dimension by eight, input rows by sixty-four and the projection cap by 4096. It also requires canonical rational input with numerator/denominator magnitudes at most 256 bits, preceded by a 78-decimal-digit allocation guard; requests are at most 65,536 bytes and certificates at most 4 MiB. Certificate rationals and intermediate arithmetic do not inherit the input-only 256-bit restriction, but the whole certificate frame remains bounded. These details are explicit in protocol.rs lines 11–12 and 35–52. A direct call to the library and a call through RC1 are different interfaces; do not silently enlarge protocol limits.

A proposed bounded RC1 packet must satisfy these existing bounds for each direction. Outside them, it must keep the explicit unsupported/resource-UNKNOWN status or use a separately reviewed interface. Resource exhaustion never certifies a lower bound, infeasibility of the mathematical model, or source nonexistence.

## 5. Directional omission counterexamples

These are hand calculations illustrating semantic scope, not executed tests or biological examples.

### Missing a source invalidates an upper bound

Take X=A={0,1}, both states with the same observation, and zero-one loss. The true randomized radius is 1/2. If the registry keeps only source 0, the pure action 0 falsely appears to have worst risk zero. It is a correct upper certificate only for the reduced source class.

### Missing an action invalidates a lower bound

Take a four-point metric space with three leaves and a center. Distances are 1 between distinct leaves and 1/2 from the center to a leaf. Let the observation fibre consist of the three leaves, while the center has another observation; let all four points be permitted actions.

Choosing the center gives worst loss 1/2. Uniform weights on the three leaf sources give mean loss 2/3 at each leaf action but 1/2 at the center. Hence the full-action minimax value is 1/2.

If the action registry includes only the three leaf actions, the same uniform source weights appear to certify 2/3, and uniform randomization among the leaves attains it. That is a different decision problem. It demonstrates why actions may not be silently restricted to the observed fibre.

### Half the diameter need not be exact

With just three mutually distance-one points as both source fibre and full action space, worst risk is 1-min_j q(j), whose minimum is 2/3. The half-diameter bound is only 1/2. Implementing “radius = half diameter” would be wrong even for this small finite metric instance.

## 6. Concrete refinement acceptance target

The next bounded target is a source-bound risk-certificate adapter around existing affine rows, with the following distinct deliverables:

1. A Lean theorem for the finite-support weighted lower bound of Section 3, retaining arbitrary X and finite A; a finite-fibre corollary using existing fibreMinimaxRadius; and an upper-witness lemma.
2. An exact table interpretation theorem for declared source and action decoders and the rational-to-real loss equality. This theorem must expose each coverage hypothesis rather than treat a caller boolean or content hash as proof.
3. A row-construction lemma equating primal/dual affine satisfaction with the stated simplex and risk conditions; optionally the explicit dual-to-strict-exclusion lemma above.
4. A concrete source instance with actual admission and observation correspondence, reusing prior R0–R4 providers. Until this is supplied, results remain “supplied-table certificate” or explicitly conditional source bounds.
5. A separately selected supported execution environment, pinned sources/toolchain and actual compiler/test receipts. Native tests, successful Lean elaboration and universal Rust refinement remain separate evidence categories.

For the full cyclic example, orbit-Hamming losses are exact rational multiples of 1/N, but equality of Fourier observations and complete action/orbit enumeration still require their own justified representation. Floating FFT equality, flattened three-dimensional coordinates, or an unproved autocorrelation rewrite is not a substitute.

For the unknown-size biological problem, a complete finite source registry is generally unavailable. The finite-support lower-bound route remains usable if all witness admissions, common decision law and full-action separation are proved. It is not an unknown-size recognizer, all-rival identifier or certificate that a searched registry is complete.

## 7. Planned validation obligations

These are specifications for a later authorized implementation pass, not claimed runs:

- A known small paired rational witness reaches the same bound by direct hand arithmetic, existing affine witness checking, and a compiled literal Lean certificate.
- Alter one matrix entry or permute an identifier without updating its semantic binding: reject or lose source-bound status.
- Drop a source: retain only the appropriately restricted upper-bound scope.
- Drop an allowed action: refuse promotion of a lower bound unless an independent full-action inequality remains proved.
- Reject malformed dimensions, negative weights, bad normalization and unsupported protocol limits. Zero weights must not activate strictness in exclusions.
- Keep shared-bank, original-ID, full-joint readout and complete-history obligations explicit; successful scalar arithmetic cannot validate them.
- Reuse existing native/control evidence where applicable. Do not repeat unrelated Quinn transport fixtures or edit the separately gated count pilot.

## Exact unresolved obligation

The mathematical certificate reduction is specified above. The missing source-to-implementation connection is still a proved interpretation of the native source, observation and loss data, with the correct directional coverage facts, followed by a verified execution/serialization relation or a separately compiled literal certificate. No amount of table parity alone supplies those propositions.
