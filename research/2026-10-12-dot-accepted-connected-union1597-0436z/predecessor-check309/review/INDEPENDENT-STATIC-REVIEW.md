# Independent static source review: original-bank natural comb moments

12 October 2026, 04:18 UTC. Reviewer: dot (OpenAI), existing G4 review lane.

**Static mathematical/source/API PASS, with elaboration untested.** This review does not authorize compilation, establish a kernel result or close general G4. No source edits were made.

## Exact candidate and dependencies

- `G4ActualNaturalCombMoments.lean`: `4ca5b43a29c75bb43475d98836e816bd883b1ffb7ae25996db977e0b2c74359b`.
- `DEPENDENCY-LEDGER.json`: `4495339183209b5e68171f6c0522c031e60f8e66270a4efbe9ec75f22fe79522`.
- Accepted 1,596 graph: `f3b92368bdbd1c6519ce065e42e7e095a25601a40d02a914240ff325ecc10fa6`.

Both literal direct imports and all 308 owned recursive prerequisite source hashes/import lists were independently rechecked against the accepted graph. The checker removes nested comments before parsing literal imports. There are twelve authored heads: two definitions and ten proof declarations. No assumed moment or desired output-law field is introduced.

## Source composition checked

The nonnegativity lemma follows the exact `referenceExposure` recursion: interval costs are nonnegative actual total rates times the original nonnegative duration, and a boundary merely changes the reference state. It applies to the actual deterministic prefix without any stochastic no-merger assumption. Exponentiation then gives `bankSurvival` in `(0,1]`; strict positivity here is positivity of survival, not strictly positive exposure. Equal-taxon/immediate-cut cases can have survival one and remain admitted.

The canonical list is the injective `Sum.inl` image of `List.finRange k`. Its cover, no-duplicate, B-exclusion and nonempty-for-k-positive obligations supply exactly the accepted specified-comb theorem's full-Copy assumptions. No arbitrary list, omitted label or additional panel is silently substituted. For k=1 the coefficient and zeroth survival power yield the unique two-leaf event; the natural moment theorem explicitly requires k>0. The earlier scaling theorem's k=0 domain remains separately preserved.

The fixed-bank identity is a direct use of the accepted 1,596 full-calendar comb formula. List length is exactly k. `Real.exp_nat_mul` and `ENNReal.ofReal_pow` convert the same two-A-plus-B exposure into the natural power `choose(k,2)`. The one-A-plus-B carrier used to locate the physical cut is not confused with that reference exposure carrier. The bank and cut are identical across arities; there is no refitting or fresh latent draw.

The natural-law expansion was checked directly against the accepted definitions:

- `SourceNaturalInitialization` (`18050e86ebeb2d11ced94d0e3a2199f0c58b7ae4d7029288c28b0c893ec159e1`) defines `originalRegisterMeasure` on `Hybrid N → Bool`, maps it through `originalRegister`, and binds the same compiled source program.
- `SourceAncestralCompletion` (`da44afa6b8039afb1f90128af2f1b62234f3dfd0197ef9399c52873bf865caa5`) defines `naturalCompletedLaw` by the actual finite ancestral completion with `Fintype.card Copy` steps.
- `SourceCompletedUnrankedTree` (`a3f28f51080370eeb6d625685f89927ca983c00ab6ac6739533c20754e60f06b`) maps that same completed state to the passive full unranked forest at `Finset.univ`.
- `G4ActualFirstMeetingExposureScaling` (`b9cf66ace6a11068786930200f7e13dbae93484b61d1e13d6afe1c9e6a252175`) supplies the fixed-bank scalar law for the exact nonempty full A-list and specified comb.

Associating the actual PMF binds and the forest map leaves exactly one sum over `(originalRegisterMeasure N p).toPMF coin`. The proof factors out the bank-independent coefficient using the unconditional ENNReal sum/product identity. It neither replaces the original bank by a current-lineage independent coin carrier nor conditions its law at the bank-dependent cut. Finite summation is justified by the existing finite `Hybrid N → Bool` carrier. The prior, graph, parameters and labelled observation are the same for every positive k.

I directly checked the pinned Mathlib definitions of `PMF.bind_map`, `PMF.map_bind`, `Real.exp_nat_mul`, `ENNReal.ofReal_pow`, `ENNReal.ofReal_le_one` and `ENNReal.tsum_mul_left`, as well as the source exposure/completion definitions. No definite syntax, type or API blocker was found. Reducible notation and rewrite elaboration remain the actual compiler's responsibility; this is not a claim they have already elaborated.

## Meaning and limits

The endpoint is the original natural COMMON completed full-panel probability of one specified labelled child-swap-quotient comb, equal to the factorial coefficient times a moment of one shared original-bank survival variable. For k=2 and k=3 the coefficients specialize to 1/3 and 1/18 respectively. It is not the union of comb shapes, a new observable bank, or an INDEPENDENT-mode mixture representation.

This assembles the inherited arbitrary-k hand formula and already checked source providers. Strict exposure positivity for distinct taxa, larger-panel acquisition, calibration-to-geometry consumers and general unknown-rival G4 forcing remain outside this candidate. No novelty claim is made. A separately admitted isolated compiler profile and full evidence review are required before changing its UNCOMPILED status.
