# Exact attainment of arc-supported infinitesimal residues

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 23:04 UTC.
Status: hand corollary of EXACT-TAIL-COMPRESSION.md, submitted for independent review. This is a source-specific sufficient criterion, not general boundary recognition.

## 1. A pure summable product is already finitely attained at a fixed cap

For the actual common Bernoulli-chain contract, suppose

    h=a lambda+sum_(i>=1) H(p_i,q_i),
    a>0, 0<p_i,q_i<1, sum_i H_2(p_i,q_i)<infinity.

Then h has an EXACT finite strict realization at that cap. If a finite two-sided factor block has full ambient rank, the earlier interior-attainment theorem applies. Otherwise one fixed nonzero annihilator covers the countable list and the exact-tail-compression theorem replaces it by finitely many strict factors. Keep a>0, so A=exp(-a) remains strictly between zero and one. In either branch no killing, Poisson approximation or baseline endpoint is used as a source factor.

This is a finite-observation theorem. It does not say that a countable convolution law itself has finite binary convolution length, and supplies no input-effective factor count.

## 2. Neutral arcs approximate a Poisson ray inside their exact value space

Let an analytic strict factor arc (p(u),q(u)), u in (0,epsilon), extend analytically to (0,r), 0<r<1. Set v(u)=H(p(u),q(u)) and V=span{v(u):0<u<epsilon}; v(0)=0. For each w>0 there are strict u_N->0 with

    N v(u_N) -> w R(r),
    N v(u_N) in V for every N.

Proof. The analytic scalar v_2(u) is positive for u>0 and zero at zero. Its first nonzero Taylor coefficient is positive, so after shrinking the interval it is strictly increasing. Choose u_N by v_2(u_N)=w/N for sufficiently large N. Since p(u)->0 and q(u)->r,

    H_j(p(u),q(u))/H_2(p(u),q(u))
      -> (1-r^lambda_j)/(1-r)=R_j(r).

Multiplying by N v_2(u_N)=w proves the limit. Each approximant uses precisely N actual strict Bernoulli factors on the same arc. V is a closed finite-dimensional linear space, hence w R(r) also lies in V. QED.

The crucial new feature is that both the residue and ALL approximants lie in the same exact value space. Ordinary approximation without this property cannot be corrected by a rank-deficient pivot block.

## 3. Exact finite realization after retained-pivot correction

Suppose a closure normal form has positive baseline, no killing,

    h=a lambda+sum_i H(p_i,q_i)+sum_(k=1)^s w_k R(r_k),
    a>0, w_k>0, 0<r_k<1,

and its retained list is summable. A SUFFICIENT condition for exact finite strict realization is the following: all but finitely many retained pairs lie on finitely many analytic neutral arcs as in EXACT-TAIL-COMPRESSION.md; let V be the sum of the complete value spaces of ALL infinitely populated such arcs. For each residual node r_k there is a neutral analytic strict-factor arc ending at (0,r_k) whose complete value space is included in V. Finitely many already-retained tangent columns span V by the analytic-arc lemma. For the fixed-critical-set setting, an infinitely populated retained arc with endpoint r_k provides the residue condition automatically.

More generally the same argument works with a finite supplied pivot certificate: its strict two-sided parameter map must lie in an affine translate of V and be a submersion onto V; all omitted retained-tail vectors must lie in V; and each residue-approximating arc must have its complete value space in V. Derivative span at one point alone does not certify the required image/value-space inclusions.

Choose the finite pivot block once. Its restricted parameter map, consisting of sums of values along the chosen arcs, is a submersion onto V at the original parameters and supplies a relative ball of radius rho>0. Preserve all finite-sampled/isolated retained factors. Truncate the countable retained arc tails sufficiently far that their omitted sum T is small in V. Approximate each w_k R(r_k) by sufficiently many strict copies along its supported arc as in Section2. Define E as the sum of the exact residues MINUS those finite-copy approximants; E is small in V. Pick the truncation and copies so ||T+E||<rho.

Adjust only the retained pivots by the exact vector T+E. Concatenate the unchanged finite retained prefix, the adjusted strict pivots and the finitely many residue-approximating strict copies. Its log signature equals h EXACTLY. The baseline remains A=exp(-a) in (0,1), all factor probabilities and ratios are strictly between zero and one, and every multiplicity is an integer. No equality is inferred merely from taking a limit; equality is supplied by the submersion correction. QED.

For several populated arcs, their pivot maps have derivative image equal to the sum of their value spaces. One combined finite block is therefore sufficient. Each selected original pivot stays present before truncation, and its allowed neighborhood is fixed before the errors are made small.

## 4. Conditional removal of a zero baseline

The same proof also handles a=0 if lambda belongs to V. Choose a small epsilon>0, add the actual positive baseline epsilon lambda, and replace the desired pivot correction by T+E-epsilon lambda. Choose epsilon and the two errors small enough for the same fixed submersion ball. This gives an exact finite source with A=exp(-epsilon)<1. If lambda is not in V, this argument does not regularize a zero baseline.

No unconditional removal of killing is established. A given small killing vector kappa 1 could be absorbed if it lies in the pivot space and its size fits the available submersion neighborhood, but no theorem covering arbitrary killing mass or the recovered cap-eight candidate follows.

## 5. Narrowed global obstruction

Conditional on the hand normal-form/compression premises, a nonattained positive-baseline, zero-killing normal form must have at least one residual term unsupported by the retained-pivot value space in the sense above. Pure summable retained products no longer supply nonattainment. Exceptional critical curves with populated neutral endpoints matching all residual nodes also do not supply it.

The remaining master obligations are still substantial: input-effective integer factor bounds; unsupported singular compound-Poisson residues; killing; and zero-baseline cases without the displayed value-space certificate. The finite normal form has no known computable total-factor bound from the input. Arbitrary-cap recognition and the cap-eight/nine candidate remain OPEN.

## Verification

This is a hand argument using the analytic-arc lemma, first nonzero Taylor coefficient, finite-dimensional closedness and submersion. No new solver or numerical fit was executed. The prerequisite complete tail-compression proof was published/read back at ee3596ecc3ce51c4d6c284a0286c8c9f86aafa15, proof blob332259042e9fdae97f226e10763e58615260f4c3. Independent review of the present corollary is requested. Earlier finite controls and QE timeouts are not promoted to a certificate for this result.
