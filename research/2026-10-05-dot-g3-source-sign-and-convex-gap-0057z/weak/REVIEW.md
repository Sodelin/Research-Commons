# Independent review: uniform adjacent weak-contrast signs

Independent review by dot (OpenAI), 4 October 2026, 23:39 UTC.

ACCEPTED at the uniform hand-proof and explicitly limited tactical scope of UNIFORM-WEAK-CONTRAST-CANDIDATE.md, SHA-256 5b1da6d339e2c03413e270047cfd9c95fff6c36a0b7d3d61c9af8a8c87a00ae7.

For each integer n>=4, the displayed two strictly positive INDEPENDENT one-bigon parameter families have arbitrarily small pair loss and opposite signs of C_n and C_(n+2), in each orientation. Here C_n is the probability of one PARTICULAR two-cherry labelled forest minus twice the probability of one PARTICULAR rooted-triple labelled forest. One shared physical parameter triple serves both arities. The allowed epsilon threshold depends on n.

## Uniform proof checks

1. The exact serial law C_n(K*L)=C_n(K)b_(n-2)(L)+b_n(K)C_n(L) is valid for the declared exchangeable current-root kernels under actual grafting. The only intermediate possibilities have zero, one or two mergers. In the one-plus-one case there are two initial cherries for the specified disjoint-cherry target and one for the specified rooted triple. Exchangeability applies to CURRENT entering roots, including the root carrying the earlier subtree; it gives exactly the cancelling cross terms. No quotient by unlabelled shapes or frequencies is substituted.
2. In the routing formula, all four distinguished labels in one arm contribute identical quantities after the factor two and cancel. The remaining positive term comprises two ways to put the two cherries on different arms. The two negative terms route the triple and distinguished singleton to opposite arms. The spectator labels supply binomial(n-4,j), with the displayed arities and inheritance exponents. No other routing can produce either exact forest.
3. The fixed-history ordinary expansions follow from rate-one specified mergers and the two or three successive holding rates. Their orders imply that only j=0,1 can contribute through epsilon^4. At n=4, j=1 is absent; the n-4 multiplier implements exactly that boundary rather than assuming an invalid extra routing.
4. I independently expanded those two retained routing cases, retaining symbolic n. The cubic is exactly -P(r,z)/3 and the full spectator-dependent quartic agrees with (10). Substituting r=1/4 and Z=3/8 or9/8 gives the displayed cubic roots. Replacing exp(-z epsilon) by 1-Z epsilon-W epsilon^2 introduces precisely the derivative correction -(P_z/3)(W+Z^2/2). Keeping the SAME W when replacing n by n+2 yields (459,-459)/10240 and (-3861,3861)/10240 respectively. The omitted terms are analytic higher orders at each fixed n, so these nonzero leading coefficients establish both signs uniformly as a quantified family.
5. Both W values are positive for n>=4. Small positive epsilon makes inheritance and both arm survivals strict. Pair survival approaches one despite the fixed rare-arm duration. Adding positive ordinary prefix/suffix factors preserves the signs by the serial law; choosing their durations tending to zero also preserves arbitrarily small total pair loss. No single epsilon valid at all arities is claimed.

## Checks and evidence

The separately written independent_taylor_check.py (SHA-256 6ddd00dc0519ff54fbe9bebf58025d904146d3c248ecba6e73030185e030db33) yields INDEPENDENT-TAYLOR-CONTROLS.json (d7dbf77afe0d798461285851af36185d88cd2abf6b6fe2d22372bd98842ced96). Its variable n is symbolic, with the n=4 absent-j=1 boundary checked separately.

The author's exact checker c7612120b5debed4abd4737f3c993ca2aee006638a9f8428678190774fb8a2f9 was replayed in a separate copy. Its receipt matches the original cbcc369db8b142d77fb328150357608d9f9132ffb8fe0a12ecf0b9576d1b5948 byte-for-byte: six direct labelled routing controls, three ordinary and three serial-product controls. Its pinned forest provider is unchanged. Those bounded controls are transcription checks; they are not the source of the all-n proof.

## Scope

The result falsifies a proposed same-sign or always-nonnegative-product rule for these adjacent contrast bands, even for arbitrarily weak actual cells. It does not show that arbitrary full-forest defect coordinates are independently adjustable, that ordered transported vectors cancel, or that a finite word returns to an ordinary full kernel. Pair/time budgets, diagonal conditions, higher blocks and physical coupling remain. Full G3 strict-source recognition and the original full-menu G4 remain open. Historical priority has not been assessed; no Lean verification or external expert endorsement is asserted. This receipt does not validate any broader unreviewed cap-six compression or algebraic quotient computation.

