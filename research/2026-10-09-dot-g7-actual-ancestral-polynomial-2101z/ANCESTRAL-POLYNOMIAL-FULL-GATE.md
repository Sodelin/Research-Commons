# Actual-source polynomial compiler gate: complete proposed argument

Contributor: dot,9 October2026. This is a formalization plan for an inherited classical/G7 path-polynomial fact, not a novelty claim or completed Lean theorem. Current draft source has no asserted final polynomial theorem.

## Target

For each actual original source N, finite copy carrier, ancestral-root admitted snapshot s and arbitrary admitted target d, construct P(s,d) in Q[X], independent of every physical rate, such that for every positive original rate bank r and every t>=0:

    sourceTimeKernel(N,r,t,s,d).toReal = P(s,d)(exp(-r.ancestral*t)).

Degree is at most choose(k,2), where k is the number of live ancestors in s. Full retained genealogy, locations and original register are retained in s,d. This is an entire transition row, not a pair statistic or selected marginal. The source-root condition is essential.

## Existing exact providers

SourceEpochRenewal.actual_source_kernel_first_jump is the actual source first-jump integral identity. SourceFiniteJumpExpansion.original_copy_cap_jump_expansion already proves finite real-merger expansion by original live-card descent. SourceActualHoldingClocks.merger_destination_card proves each genuine merger drops live cardinality by one; SourceAncestralCompletion.ancestral_merger_preserved proves root support. UnifiedLean.G6.AncestralRateFree proves each actual root Choice has population none and rate r.ancestral/2, including both orientations of each pair. These are authenticated baseline181 providers; their old UNCHECKED headers do not override the later actual baseline replay.

The only remaining counting identification here is the explicit bijection of actual Choice with ordered distinct pairs of live ancestors. Thus there are k(k-1) choices, total rate rho*choose(k,2). No unordered-path normalization is silently substituted.

## Construction and proof

Induct on k. If k=0 or1, Choice is empty and the actual first-jump equation gives the identity row for every time; take the constant indicator s=d. This includes empty copy panels and t=0.

For k>=2 put n=choose(k,2). For each actual ordered choice p let s_p be its actual source destination. By induction P(s_p,d)=sum_m a(p,m) X^m, with m<=choose(k-1,2)<n. Define

    P(s,d) = [s=d] X^n
      + (1/2) sum_p sum_m a(p,m) (X^m-X^n)/(n-m).

Every coefficient is rational. Every denominator is a positive integer, and every exponent is at most n. This is a finite construction over the actual original Choice carrier and actual source destination. It is independent of r; there is no fitted transition matrix.

The first-jump equation has holding term exp(-rho*n*t)[s=d]. For each choice its integral term is

    integral_0^t exp(-rho*n*u)*(rho/2)*P(s_p,d)(exp(-rho*(t-u))) du.

Finite linearity and direct exponential integration give, for m<n,

    integral_0^t exp(-rho*n*u)*(rho/2)*exp(-rho*m*(t-u)) du
      = (exp(-rho*m*t)-exp(-rho*n*t))/(2*(n-m)).

The positive rho cancels exactly. Substituting the induction hypothesis yields the displayed polynomial. No convergence or limiting interchange is required. Each primitive vanishes at X=1, giving the correct time-zero row. Terminal snapshots have constant identity rows. Nonnegativity and row normalization on X in(0,1] follow from the proved actual-source equality; they are consequences, not construction assumptions. Finite readout pushforwards are obtained by summing these same row polynomials.

## Full G7 connection and remaining gates

This closes the arbitrary-size single-population analytic kernel once formalized. It does not alone identify a complete graph law with the existing joint-frontier Python compiler. Needed afterward:

1. transport a whole-population forest into the source-root representation without losing carried descendant trees or shared register;
2. instantiate inherited G1ActualJointEpoch.actual_separated_joint_epoch_law on the actual entering population partition, then reassemble the complete joint forest;
3. use actual source scheduling/semigroup identities to combine each physical edge's interrupted epochs into its one survival variable;
4. combine the already source-exact original-ID control kernel with one shared parameter bank, translating Python parent0 probability g=1-gamma_Lean;
5. retain exact planar admission, rank/budget and whole-history policy obligations after the compiler.

The G6 worker is materializing the authenticated minimal G1 joint tensor closure once for shared reuse. Generic actor commutation is insufficient unless the actual physical partition and agenda are bound to it.
