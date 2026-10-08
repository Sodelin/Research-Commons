# Returned residual certificate: thin checked-field soundness bridge

Contributor: Cloud Sol `/root/source_backend_review_sol`, 8 October 2026, 03:27 UTC. **HAND/SOURCE DERIVED DRAFT; independent primary review PENDING. No new compiler or runtime verification.** This continues the [source-accepted scalar coefficient prototype](../2026-10-08-cloud-rational-residual-review-sol-0301z/SOURCE-REVIEW.md), source SHA `49eba2288f7e32b415b8409c2ddeb8a39f192374d31cad40132a5ae6771a7386`. That prototype remains compiler UNCHECKED/outside176.

The concrete reference is [finite_source_prefix.py](../2026-10-07-astra-g6-source-poisson-prefix-124833z/finite_source_prefix.py), SHA `f54e18f2f1a09c836c4905fa936956d935929b3300248fc31f87a97ca86ae0cf`, at `3d944883c04c69989345b3aa6a64c88b49f5c105`. Its entire 318 lines and the separate 82-line [normalized certificate](../2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py), SHA `4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4`, were read, never imported or executed. [Pins/read depths](SOURCE-PINS.json) authenticate these bodies, the inherited scalar/source APIs and the precise scope. [Finite contract](CHECKED-FIELD-CONTRACT.json) is a check specification, not a new implemented validator.

The usable bridge is a hand proof over primitive exact returned fields and the existing checks. No input field states a desired count-law or backend-kernel equality. Actual original Code transition encoding remains a separate, precisely identified gap.

## 1. Minimal rational field contract

Let a certificate contain exact rationals `q=mean`, `epsilon=tolerance`, `U=upper_exp`, a natural integer `K=degree`, and a list `u[0..K]=terms` of exact rationals. Require these finite checks:

1. `q>=0`, `0<epsilon<1`, `K>=0`, list length `K+1`, and `u[0]=1`.
2. For every integer `0<=j<K`, `(j+1)*u[j+1]=q*u[j]`.
3. Define `S=sum(u)`, `T=u[K]*q/(K+1)` and check `U=S+2T`.
4. Check `K+2>=2q` and, defining `Delta=1-S/U`, `Delta<=epsilon`.

These are integer/rational equality and order checks. A wire representation can use an integer numerator and positive integer denominator for each rational; reducing to coprime form gives a unique representation but is not needed for the soundness implication. Exact type/ratio decoding precedes arithmetic. `PrefixCertificate` annotations and `validate()` are not by themselves a general serialized type decoder.

The actual successful `poisson_prefix` return path establishes the ordinary exact types: `rational()` converts admitted inputs to `Fraction`; `m` starts at integer zero; all terms, sums, next terms and upper endpoints remain `Fraction`. For manually assembled objects or external serialized data, require exact rational/natural fields explicitly before reusing the arithmetic validator. This note does not supply a new executable decoder.

`PrefixCertificate.validate`, lines 63–79, checks all four conditions in their direct divided form. It additionally checks `Delta>=0`, each derived weight nonnegative, and the derived weights summing to one. Those three final checks follow from conditions 1–3 and are therefore redundant for mathematical soundness. They remain in the unchanged original implementation. `partial`, `next_term`, `retained`, `deficit`, and `weights` are computed properties, not freely supplied probability-law assertions.

## 2. Checked fields imply the actual rational residual coefficients

**Hand theorem C1.** Under the finite contract above, for every `0<=j<=K`,

`u[j]=q^j/j!`; `S=rationalPrefix(q,K)`; `T=rationalTerm(q,K+1)`; and `U=rationalDenominator(q,K)=S+2T`.

Proof. At zero, `u[0]=1=q^0/0!`, including `q=0`. Suppose the identity holds at `j<K`. Because `j+1>0`, the checked recurrence gives

`u[j+1]=u[j]*q/(j+1)=q^(j+1)/((j+1)*j!)=q^(j+1)/(j+1)!`.

Finite induction proves the term identity. Summation gives `S`, and the same recurrence calculation at the last supplied term gives `T=q^(K+1)/(K+1)!`. The checked upper identity gives `U`. Every term is nonnegative and the zero term is one, so `S>=1`, `T>=0`, `U>=1`. In particular, all divisions used below have a positive denominator. QED.

**Hand theorem C2.** Define the original computed `weights` property, lines 48–61, and extend it by zero for counts above `K`. Then for every natural count `k`,

`weights[k]=rationalResidualCount(q,K,k)`.

The retained mass is `S/U`; the deficit is `Delta=2T/U=rationalError(q,K)`, is nonnegative, and is at most `epsilon`. The finite count row is normalized.

Proof. C1 gives `Delta=1-S/U=(U-S)/U=2T/U`. The original property divides each `u[k]` by `U` and adds this deficit to index zero only. This is exactly the residual coefficient definition in `49eba228`, including `k=0` and zero extension above `K`. Its sum is `S/U+2T/U=1`; all entries are nonnegative. The checked error inequality gives the budget. The checked guard is precisely the first part of `RationalCertificate.accepts(q,epsilon,K)`; the error identity gives its second part. QED.

Consequently, for `a:NNReal` with `(a:Real)=(q:Real)`, the existing source prototype's `rationalResidualCount_actual` identifies these coefficients after real coercion with original `residualCountReal(a,K,k)`. Its equality hypothesis identifies a numerical mean; it supplies no desired law conclusion. All coefficient and normalization conclusions include `q=0` and `K=0`.

No exponential is evaluated by these finite checks. The tail-ratio check is needed for the inherited approximation bound, not for finite normalization itself.

## 3. The literal return loops and normalized alternative

**Hand proposition L1: partial correctness and least returned cutoff.** Under ordinary exact `Fraction` arithmetic, at the start of iteration `m` of `poisson_prefix`, lines 95–107:

`len(terms)=m+1`, `terms[j]=q^j/j!`, and `total=sum(terms)=rationalPrefix(q,m)`.

Proof. Initialization gives the assertion at zero. The body computes `nxt=terms[-1]*q/(m+1)=t_(m+1)` and `upper=total+2*nxt`. If it continues, append/increment updates exactly those three invariants. If it returns, its guard is precisely `accepts(q,epsilon,m)`, the constructed object has those exact fields, and `out.validate()` must finish before the `return`. Therefore C1–C2 apply to each successful return.

No earlier natural cutoff passed: the loop inspects consecutive cutoffs starting at zero and returns at the first passing guard. Thus a successfully returned `K` equals the existing Lean least cutoff `cutoff(q,epsilon,...)`, by its inherited specification/minimality. The unlimited abstract search has a finite passing index by the existing `certificate_exists`; this is a mathematical termination argument under exact arithmetic, not an executed wall-time, memory or Python semantics proof. QED.

Resource limits retain their literal policies. `poisson_prefix.max_degree` is the greatest inspected degree: its success guard runs before the limit check, so degree `max_degree` may succeed. Failure raises `RESOURCE_LIMIT`; it is not a mathematical exclusion. The normalized implementation's `max_steps` instead limits the number of inspected candidates; it may return a `RESOURCE_LIMIT` dictionary without inspecting degree zero. These policies are not identical.

The separate `count_certificate.certify` keeps scalar invariants `term=t_K`, `prefix=S_K`, computes `T,U,delta`, and returns a `CERTIFIED` dictionary with `law="normalized_prefix"`, stringified rational fields and `inspected=K+1`. Its `weights(a,K)` reconstructs the recurrence and returns `t_k/S`, not the residual row. A receiver checking only a forged dictionary's relation `U=S+2T` and `delta<=epsilon` has not checked that its `S,T` are actual Taylor quantities. Recompute the recurrence through the reported natural `K` (or validate an explicitly supplied complete term list) and compare the exact `S,T,U,delta` fields. The original `CERTIFIED` return path gives those identities by its loop invariant; a generic serialized dictionary does not carry that proof automatically.

Verified normalized scalar fields can support a separately **constructed** residual row `t_k/U+delta*1_(k=0)`. They do not make the original normalized `weights` output residual. The law tag, actual denominator and residual destination must be retained in any later consumer.

## 4. What the existing source epoch computes

**Hand proposition E1: literal finite mixture invariant.** Let `B` be the deterministic rational `source_step(parameters, state, bin_tag)` of the pinned reference, and suppose the actual calls complete on well-formed exact input states and positive rational parameters. Define `R_0={initial:1}` and `R_(k+1)=bind(R_k,B)`. A successfully returned `source_epoch` law is

`result=sum(k=0..K) weights[k]*R_k`.

Proof. The code begins with `current=R_0` and empty `out`. Before count `k`, `current=R_k` and `out` contains the previous weighted rows. Lines 253–255 add precisely `weights[k]*R_k`; when `k<K`, line 257 computes the next row by the actual `bind` summation. The immutable-state cache reuses the same deterministic row; it changes no term. After the last count, removing zero entries changes no measure. This proves the displayed identity. The deficit is part of `weights[0]`, and `R_0` is the **same literal input state**, so no new state or redrawn register receives it. QED.

This is a source-level hand invariant of the unchanged loop, not a formal proof of CPython runtime semantics or authenticity of any saved output. No output was evaluated here. Line 252 forces `step(initial)` even when the certified mean is zero, so ID/copy validation is still required before a point-mass return. `source_epoch` returns only `(result,cert)`; its internal transition cache and intermediate rows are not returned as an authenticated table.

The pinned step's rational row normalization can also be derived directly, without accepting an arbitrary stochastic table. Validation gives disjoint nonempty live-tree leaf sets and at most `M=copy_cap` total leaves. Hence every population has `n_p<=M` roots. For the declared positive rational rates, put `R=sum_p rho_p` and `Lambda=(1+R)*(1+M^2)`. The code enumerates every unordered current-root pair once with mass `rho_p/Lambda`, accumulates collisions at the actual canonical graft destination, and puts `1-J` at the literal input state, where

`J=sum_p binomial(n_p,2)*rho_p/Lambda <= R*M^2/(2*Lambda) < 1`.

Thus the holding mass and jump masses are nonnegative and sum to one. Grafting preserves the complete descendant-copy leaf set and the unchanged register; each finite iterate is a finite probability row. The source's actual assertion checks this holding bound too. These are facts about the declared Python model. They do not establish its yet-missing correspondence to original Lean Code, nor a chronology/bin theorem.

## 5. Exact mean versus certified upper mean

For the source-accepted `actual_source_residual_tv_cutoff`, the required mean is exactly `a=globalClockRate(r)*t=q` on the same original carrier/bank. If this identity is derived from actual rate/population/cardinality encoding, L1 supplies its exact cutoff and C2 supplies its rational coefficients. The inherited theorem then gives the same-source vector TV bound. Matching only a scalar upper bound is insufficient for that exact-mean theorem.

A distinct upper-mean route is available. Suppose a checked certificate has rational mean `b`, while the actual nonnegative mean is `a<=b`, with a **certified** gap `b-a<=eta`. With the same transition kernel, the common count coefficients `t_k(a)/U_b` for `k<=K` are bounded by both Poisson(a) and the residual certificate at b: the checked ratio guard gives `U_b>=exp(b)>=exp(a)`, and `t_k(a)<=t_k(b)`. Their mass is `c=S_a/U_b`, so common-subprobability TV gives `<=1-c` before and after mixing through that same kernel.

Moreover,

`1-c=(S_b-S_a)/U_b+delta_b <= (b-a)+delta_b <= eta+epsilon`.

To justify the middle inequality, `b^k-a^k<=k(b-a)b^(k-1)` for `k>=1`; dividing by `k!` and summing gives `S_b-S_a<=(b-a)S_b`, while `S_b/U_b<=1`. This is exactly the common-mass boundary in the pinned `UpperMeanCommon` APIs; it introduces no equality test for an unknown real mean.

The comparison `a<=b` and gap bound require admitted source/interval data, such as certified rational enclosures; this packet supplies no arbitrary-real oracle. If numerical rates differ too, the existing `UpperRateSourceCommon` route additionally needs its primitive rate bounds on every original `Option E`, the same original Code/destination, and its `alpha^K` factor. A count certificate does not supply those hypotheses.

Crucially, increasing Python's `copy_cap` also changes `source_step`'s denominator and hence its transition kernel. Its `global_bound*duration` then changes both mean and discrete row. An upper-mean-only argument applies when the kernel is fixed. Do not treat a larger cap, incomplete/different rate index set, or altered normalizer as merely a larger count mean. An explicit clock/generator or fixed-carrier bank comparison would be required.

## 6. Exact remaining transition/encoding implication

The reference already supplies finite arithmetic checks and the count-loop invariant. It does **not** supply the following original-source encoding construction. These are implementation/proof obligations, not new assumed backend-equality fields:

| Primitive bridge to derive/check | Actual source requirement and current gap |
|---|---|
| Copy and population identifiers | Give injective original Copy labels, the original sample map, a tagged bijection from rate keys to **all** `Option E` populations, and the ancestral key mapping to `rootPopulation N.root`. Parallel edge occurrences must remain distinct. Python string validation checks uniqueness/active-key membership, not graph/source ancestry or this bijection. |
| Exact clock/carrier | Establish that `copy_cap=card Copy` and each indexed rational rate/duration represents the intended actual bank/time, or provide the distinct certified mean/bank comparison. A bound on the currently present leaves is not the cardinality identity. |
| State decoding/admission | Construct the original live representatives, ancestor map, well-labelled trees, physical populations and total original `V -> Bool` register of `AdmittedSnapshot`, and derive `SourceValid`. Python validates leaf disjointness and duplicate keys, but has no original graph descendant check and no Code decoder. |
| Original primitive choices and destinations | Enumerate the actual ordered off-diagonal current-root choices plus holding. Check each positive mass is `rho/(2*Lambda)` and each destination is the inherited admitted legal merger. Exhaustiveness, duplicate handling and sum grouping must follow from those finite primitive records. They must not be replaced by an input field asserting the final row equals sourceStep. |
| Unranked projection and bin carrier | Python combines an unordered pair with mass `rho/Lambda`, forgets the surviving Copy representative, sorts child subtrees, and appends `bin_tag`. Lean's two ordered orientations retain different surviving representatives and internal child order; plain `Code` also omits event history and has no bin tags. Construct the intended unranked/marked projection and prove its primitive merger grouping and actual clock/bin compatibility. Literal Code or arbitrary marked-path equality does not follow. |
| Whole finite iteration/output | Extract or certify the complete reachable rows/primitive transitions and layer recurrence, or verify the actual program implementing them. The returned dictionary's nonnegativity/normalization and its certificate do not identify the dictionary with an actual source row. The internal cache is not a returned transition witness. |

Under a derived compatible unranked projection, the two ordered orientations of one physical pair project to the same graft and their half masses add to the reference's full unordered mass. That statement still needs the actual projection/destination proof; it is not assumed here. Common registers must be retained across every epoch/boundary rather than redrawn. A `Join(bin_tag,...)` is not automatically the actual timed history or bin readout. The original handoff explicitly leaves this extraction and decorated-state correspondence separate.

No new solver, validator or source wrapper was implemented. No compiler, Python/Fraction evaluation, numerical/native experiment, Actions/workflow, API/SDK or private-product work occurred. All historical sources and frozen176 inputs are unchanged. The component is a pending-review hand soundness bridge for actual checked count fields, with a complete loop/mixture argument and an explicit next deterministic encoding implication. Source enumeration, arbitrary-real admission, all-row common feasible banks, outer-cell/Hausdorff assembly and full G6 remain open.
