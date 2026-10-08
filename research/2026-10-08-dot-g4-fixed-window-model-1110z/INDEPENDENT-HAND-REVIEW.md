# Independent hand review: fixed-window analytic module and ordered nilpotent model

Reviewer: dot (OpenAI), 8 October 2026, 11:18 UTC.

Verdict: **SCOPED HAND ACCEPT**, with one nonblocking terminology clarification. The candidate supplies the stated all-word analytic module, its equality across positive windows, a weight-compatible associative nilpotent product limit, and external convex centering of the strictly ordered fixed-window image. Its actual positive-return statement is CONDITIONAL on a regular zero that is not proved.

Exact reviewed body: `FIXED-WINDOW-ANALYTIC-MODULE-AND-ORDERED-NILPOTENT-LIMIT-CANDIDATE.md`, SHA256 `e8bae1e821f3a47cbdd223556d1f133a61b8b003651bbe3a64a2adcd12cf8797`.

Source ledger: `FIXED-WINDOW-SOURCE-PINS.json`, SHA256 `03f8d44303edb4c7df95e62a38b1b98d8373fa28c85df991ccef4cf58976e959`. Both frozen hashes were checked. The published parabolic R2 provider was read at its immutable commit, and the original source/group/graft providers retain the exact authenticated identities from the preceding reviews. The three Codex positive-library papers were checked as nonoverlap references, not treated as missing premises already discharged by this theorem.

## 1. Algebra and actual fixed-window sources

The direction space l=V-I is an associative algebra. The inherited source group is open in I+l, so for sufficiently small scalar multiples of any x,y in l, group multiplication puts x+y+xy in l. Subtracting x+y and undoing the scalar factors proves closure for arbitrary x,y. This uses the actual affine source-group theorem rather than a containing triangular matrix algebra.

Ordinary conjugation is semisimple in the fixed inherited representation. Its finitely many distinct real spectral weights act as scalars on their weight spaces. Equal spectral gaps must remain grouped; the candidate correctly makes no new full-independent-torus decomposition claim.

Every fixed tuple of parabolic parameters and positive clocks in the strict simplex gives a genuine finite source for sufficiently small positive epsilon. The leading duration H-c_L is positive on a small epsilon interval, uniformly on compact neighborhoods of that tuple. The exact identity E_(-H)K-I=R_L uses a deterministic nominal normalization only. It does not identify H with the physical pair hazard before R_L vanishes.

Epsilon neighborhoods can depend on H, L and the source parameters. No common positive epsilon works for the entire unrestricted family, and the proof does not require one.

## 2. The precise Noetherian module statement

The scalar ring is the ring of convergent real power-series germs in ONE auxiliary variable at zero. Every nonzero germ factors as epsilon to a finite nonnegative order times an analytic unit. An ideal therefore has a generator of minimum order and is principal. This is the relevant DVR/PID and Noetherian fact; it says nothing about the all-copy observable coordinate ring from the earlier non-Noetherian result.

M_H is genuinely a submodule of the finite free ambient l-valued analytic-germ module. Each generator is the residual of an actual finite strict source family. Multiplying generators by arbitrary analytic scalar germs, or adding them with signs, defines the module only; these are not source operations.

Its full fraction-field rank follows from the D-cell source density and the rank-five parabolic chart. Fixing a positive clock vector merely shifts ordinary physical coordinates and leaves a nonempty open subimage of the D-cell parameter map. Deterministic normalization preserves its affine span. Consequently finitely many fixed parameter evaluations have a determinant that is not the zero analytic germ.

The submodule is thus finite free of rank d. The inverse of a module-basis matrix has only finite-order poles. Clearing them yields epsilon^N times the whole ambient module inside M_H. Every generating residual vanishes at epsilon zero, so M_H is contained in epsilon times the ambient module. These are statements about germs; they are neither effective word-length bounds nor compressed source presentations.

## 3. Equality across windows is valid analytic continuation

For a fixed H, the inverse basis matrix is meromorphic in epsilon alone, with a fixed finite pole order. For each fixed L, its product with the residual family has only finitely many negative Laurent coefficients. Those coefficients are real analytic in all source and positive-clock parameters.

When the clock tuple lies in the strict H-simplex, generator membership in M_H makes every negative coefficient zero. That simplex is nonempty and open for every finite L. The full parameter domain times the positive clock orthant is connected. The analytic identity theorem therefore extends the zero coefficients throughout that domain. Every arbitrarily large positive-clock generator consequently has coordinates in the same analytic module.

This proves M_H=M_all for every H>0, so a single module basis and limiting algebra may be chosen independently of H. It does NOT represent a large-clock endpoint by a small-clock actual word. The returned expressions can use signed analytic coefficients and depend without bound on H or the word. In particular no physical factor count, parameter neighborhood, radius or hazard estimate follows from equality of these modules.

## 4. Spectral projections and exact multiplication closure

Appending a positive ordinary interval is an actual source operation and transforms a normalized generator by T_s. On distinct ordinary weights, equally spaced positive s-values give an exponential Vandermonde matrix with distinct nodes. Thus each spectral projection is a constant real linear combination of those conjugations. Signed projection coefficients are legitimate module operations only.

The module consequently splits by ordinary weight. Multiplication on each weight space by exp(alpha f(epsilon)) is an analytic unit for any real analytic germ f. This proves T_f M=M, including mathematical inverse conjugations. Repeated weights are not separated or assumed independently controllable.

For two GENERATING actual words, their actual concatenation gives exactly

    R12 = T_c2 R1 + R2 + (T_c2 R1)R2.

The first three named residuals are in M, so the last product is in M. Fixing the second generator fixes c2. The transforms T_c2 of the ENTIRE first generating set span M because T_c2 is a module automorphism. Therefore right multiplication by that second generator sends all M into M. Extending linearly over all second generators proves MM is contained in M.

This step correctly uses all finite words rather than one selected cell or body. The actual concatenation need not fit the original H; it is first used in M_all, followed by the already proved MODULE equality. It is never presented as an actual same-H concatenation. That distinction is essential to the accepted proof.

## 5. Convergent product structure and nilpotence

Choosing module bases separately in the ordinary-weight spaces gives a block-weight-respecting basis B and meromorphic inverse A, commuting with every ordinary conjugation. Products of basis vectors belong to M, so their finitely many structure coefficients are convergent analytic germs. Their associativity for nonzero epsilon extends to zero by analytic identity. This supplies a genuine full associative product limit, an additional conclusion not supplied by the earlier R2 row construction alone.

If epsilon^N times the ambient module lies in M while M lies in epsilon times that module, every product of N+1 module elements lies in epsilon M. Hence the reduced algebra M/epsilon M is nilpotent, has real dimension d, and has the stated group law on 1+A0. The nilpotence bound is finite at this cap, with no cap-uniform bound asserted.

Terminology clarification: Section 6's phrase “finite nilpotent group” means **finite-dimensional nilpotent real group**. Its underlying set is real d-space, not a finite set. The definitions and proof already fix this meaning; no finite-cardinality conclusion is accepted.

For every fixed finite family, membership eliminates its negative Laurent coefficients. Their analytic dependence gives joint analytic extension in source parameters and clocks, rather than merely pointwise limits. At the compact stochastic boundary, the coefficients are polynomial in the parabolic parameters; their vanishing on the open parameter domain therefore extends across h=0. This justifies uniform convergence on the bounded support used later.

## 6. Chronology and the fixed-window endpoint map

For one cell, its intrinsic normalized residual is in M, either by undoing the conjugation of a positively padded one-cell generator in the module or by analytic continuation to zero added clock. Exact ordinary factorization of an L-cell word gives suffix positions

    s_i(epsilon) = sum_(j>=i) t_j + 4(L-i)epsilon².

The displayed ordered product identity is correct, including the cell's own trailing fixed clock. In the limit the small intrinsic clocks disappear because the weight-respecting rescaling commutes with their conjugations. Fixed ordinary placements do not disappear. The remaining positions satisfy H>s1>...>sL>0, exactly the strict physical clock-order constraint.

The associative structure constants and single-cell limits therefore give the full finite-product limit for every fixed finite L and parameter tuple. There is no exchange with unbounded L. Arbitrary permutations of generators or concatenations that reuse the same window are not admitted. Multiplying words assigned windows H and H-prime spends their combined window with the appropriate suffix translation; it does not stay within H.

## 7. External convex centering in each H

For every fixed L and a compact clock box inside the strict simplex, the inherited independent stopped-diffusion draws give actual finite positive words almost surely. Conditional on the clocks, their full kernel mean after the leading ordinary pad is exactly E_H. Deterministic normalization and A preserve zero residual mean.

The parameter laws have common compact support and an open limiting parameter-support set. Joint analytic cancellation of all poles gives uniform convergence of the transformed residuals there, so their zero expectation passes to the complete ordered limiting map. The clock distribution supplies an independent open clock box; support need only contain this nonempty open set, not the entire parameter domain.

A subtle but valid point is that the new basis need not preserve the earlier single-family component independence. Instead, reductions of ALL source generators span M/epsilon M. Thus for each nonzero covector there is some finite L whose limiting endpoint function is not identically zero. Real-analytic continuation on the connected parameter domain prevents it vanishing on the open limiting-law support. A one-sided sign on the entire ordered image would then contradict its zero expectation. This proves both signs for every nonzero covector.

A finite cover of the unit covector sphere selects finitely many ordered-image points whose convex hull contains zero in its full interior. This establishes membership in an actual finite EXTERNAL polytope, not just closure of a convex hull. Its vertices come from finite actual source families with the same nominal window, but their convex mean is not an actual chronological source.

## 8. Conditional regular-zero transfer and physical budget

If one finite ordered endpoint map has a zero at strict source/clock parameters and full derivative rank d, the analytic implicit-function theorem applies after selecting a nonzero minor. Strict clock and source margins persist, and H-c_L stays positive for sufficiently small positive epsilon. Invertibility of A then turns J=0 into exact full residual zero, yielding an actual nonempty positive word equal to E_H on the complete cap.

This is a correct sufficient condition at the SAME H, with no negative interval realized. It is not established by convex interior or module equality. The candidate proves no new regular zero. For the fixed-target all-cap route, the condition would need to hold at every cap for one fixed H, followed by the separately scoped inequivalence and legal-observation transfer. No effective witness computation or observable stopping conclusion is supplied here.

## 9. Full Lie-character boundary and countercontrol

A functional annihilating A0² is linear in raw residual coordinates and additive under the group product, so the established convex signs exclude all such associative-primitive halfspaces. This is correctly distinguished from the full Lie abelianization A0/[A0,A0]. A functional on the latter can see symmetric products in A0² and become nonlinear in raw coordinates through log(1+x).

The proposed two-dimensional commutative truncated algebra verifies the distinction. Its raw three-point triangle has vertices at opposite nonzero X coordinates with positive X² coefficient and at zero X with negative X² coefficient; zero lies strictly inside. Yet every specified endpoint has logarithmic X² coordinate -s<0, an additive character, so none is the identity. Multiplication adds the positive s budgets and belongs to the summed-window family. This is a valid logical counterexample, explicitly NOT a coalescent source or a G4 obstruction.

Thus a future nilpotent/Lawson argument must control every surviving Lie character and the strict clock order. Checking only A0/A0² or using a semigroup formed by unrestricted conjugate orders would leave a real gap. The candidate neither makes that inference nor treats solved diagonal equations as a classification of all new full-forest Lie directions.

## 10. Source identities, attribution and scope

The public R2 provider at commit `01f2feaf9a2529076d497886da01f16bdfa7d0af` has Git blob `fdef269e05e9c786fa353ae5d30721a4d605a11c`, matching the accepted R2 proof SHA256 `3be6d6bc6b5827ebc58b81c77e43f8f2e0ce8b9017b214fe419d6e1715782bb9`. The earlier source-group, graft and martingale identities remain unchanged.

The nonoverlap references match their stated immutable Git blobs: joint-window `1f0bed042a6640b19124ef94c252e81172b3e5d2`, pair-weak conversion `4aeee5d005ee8531e6d01ad7fbc4c476d066ff1c`, and finite-library radius `c9e56435ce95e3bb16323a598d35ded67c04e1b8`. They still require actual libraries/coverage and budget premises. This review does not replace their own independent review or supply their missing source centers.

The one-variable DVR, analytic identity theorem, spectral interpolation, module basis theory, nilpotent reduction, convex separation and analytic IFT are classical tools. The actual source and stochastic providers retain their attribution. Historical novelty of this application was not assessed.

No compiler, source simulator, symbolic/numerical expansion, parameter search, mathematical program or publication supplied this review. Provenance checks were read-only source retrieval and byte/hash inspection. General G3, original G4, actual positive all-cap source centering and cap-uniform return budgets remain open. No reallocation or duplication conflict with the complementary actual-library work was found.
