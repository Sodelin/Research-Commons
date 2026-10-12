# Independent static review: actual original-bank certificates

12 October 2026, 04:44 UTC. Reviewer: dot (OpenAI).

**Scoped static source/API PASS. No compiler has been invoked for this candidate.** Elaboration, generated declarations and terminal audit remain separate gates.

The final source is `G4ActualObservableBankCertificate.lean`, SHA256 `92486cb1efd96e9d538b52de511840b852725a2ee1d5c4fa4e00ce717e41f3b1`. The dependency ledger is `f67e5c71d810eca931558a56b61c87934058fe35d9ae1a52779866b2de334933`. I independently rehashed all 309 selected 1,597 prerequisite bodies, checked every literal import against the accepted graph `0af3a801949ed839ebf9b515e67f3b40c92fb9c11df92e849bf002f1ecdbca4d`, and recomputed the complete owned import closure. The source has twenty authored declaration heads, including seven definitions. The external polynomial import was read at the exact accepted Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

## Source and probability semantics

The real weights are exactly the masses of `(originalRegisterMeasure N p).toPMF` on the finite original `Hybrid N -> Bool` bank. `GProgram.G5.StrictBoundaryRoutes.strict_original_register_coin` (provider `4b736aef084f03f530d7cc8daeeaede72842c6f9f6989a6e4f53f60ce68597ac`) supplies full support directly from the original positive and below-one hybrid probabilities; its use does not require a StrictWord premise. `SourceEpochSemigroup.pmf_sum_real` (provider `845739bc6b110eadd611e0133906ec3f9b036d66f17902f46885c660213b179f`) supplies normalization. There is no fresh bank, changed posterior, independently indexed coin carrier or graph-size bound.

The source reuses the checked natural moment endpoint `cccfa223a8e74e37e54ce8d7b07bcb0193bbb8422ff2e8e99bf6dcc4c17d9d2c`. The original graph, calendar, registry, rates, taxa and once-drawn bank remain fixed across arities. Real survival lies in (0,1]; the finite positive normalization coefficient is the specified-comb coefficient `2^k/((k+1)! k!)`. Converting the finite ENNReal sum to real numbers is valid because bank masses and survival powers are finite. The actual moment identity is asserted only for k > 0, retaining the exact canonical full Copy-panel event.

For a supplied sparse polynomial nonnegative on [0,1], the finite sum interchange gives its expectation as the supplied linear combination of actual normalized observed probabilities. Every summand is nonnegative and every original bank weight is strictly positive. A zero expectation therefore forces the polynomial to vanish at each actual bank survival. The nonzero-polynomial root-set corollary uses the finite multiset of real roots. It proves certificate soundness, not existence, discovery, effective root extraction, support-size recovery or stopping.

For levels 1,2,3 the exponents are 0,1,3. The polynomial identity is `(x-a)^2*(x+2*a) = x^3 - 3*a^2*x + 2*a^3`. Normalization and the two calibrated moments make its expectation zero. Nonnegativity of a and strict positivity of actual x rule out the second factor vanishing. The forward conclusion therefore holds for every original bank, including an empty-hybrid bank and the equal-taxon X=1 control. The reverse direction substitutes the constant bank survival into the actual third moment and uses the same weight normalization. The final equivalence is precisely `18*d = (3*c)^3` iff each bank survival equals `3*c`, with c and d the actual specified three- and four-copy comb probabilities. No strict-exposure assumption is needed.

## API and revision check

The original frozen source `b841ddcce57bcfa680a0db999ff31d86ae04ac75fd2588b1e28631f999028aa1` lacked the namespace containing `toUnranked`. The final exact diff adds `open UnifiedLean.Source.UnrankedGenealogyObservation` and the requested reverse-equivalence theorem plus its axiom-report command. The previous arguments and statements are otherwise preserved. I directly checked `ENNReal.toReal_pos`, `toReal_le_of_le_ofReal`, `toReal_sum`, `pow_ne_top`, `Polynomial.mem_roots` and the existing `eval_finset_sum` alias. The latter alias is deprecated in this Mathlib version but still present. No remaining definite syntax, type or API blocker was found by static inspection; tactic normalization still awaits actual elaboration.

## Attribution and remaining scope

This is a source-faithful implementation of inherited ALL-CAP D2 certificate soundness and the original paired natural-tree calibration argument. It introduces no new mathematical priority claim. It does not assume an abstract desired observation law or supplied two-arm decomposition. The finite list of polynomial levels and its nonnegativity/zero expectation are explicit input certificates; a general search algorithm is not supplied.

The source concerns canonical repeated-copy natural COMMON observations. Arbitrary larger-panel copy transport, programmed-row adapters, two-direction route geometry, INDEPENDENT transport, sparse-certificate existence/termination, joint-tree weight recovery and full G4 finite forcing remain separate. The cubic equivalence alone does not finish the paired ordinary-tree branch or general G4. No publication or accepted-union promotion follows from this static review alone.
