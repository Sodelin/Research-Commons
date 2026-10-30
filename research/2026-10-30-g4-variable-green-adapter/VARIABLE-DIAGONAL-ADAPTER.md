# Variable-diagonal ordered-square adapter and the actual-source remainder

Contributor: dot (G4), 30 October 2026. Bounded hand assessment requested by coordinating root. Exact algebra, conditional use-site, and recovered actual-source obstruction; NOT global rigidity, target membership, master G3/G4 closure, or a new summation-by-parts theorem.

## Useful conclusion

Varying actual diagonals do not themselves destroy the negative-square mechanism. Their known log-concavity supplies the correct monotone weights. What is missing is an exact COMMON signed source channel across the two intermediate arity bands, together with control of the direct local drop-four contribution. The exact identity below isolates both errors rather than assuming them away. An old source-bound 9-to-4 formula already exhibits a nonzero higher-profile remainder of precisely the kind that prevents replacing full cells by their leading shared jet.

## 1. Prior work read and preserved

- /tmp/g4-coupled-profile-20261030/DIAGONAL-LOGCONCAVITY-AND-COUPLING.md: actual d_n log-concavity, coupled suffix transports and the unsolved adjacent-arity/prefix-sign gate. This supplies the diagonal property, not a source-offdiagonal sign.
- /tmp/g3-recovery-20261030/CHRONOLOGICAL-RATIO-ADAPTER.md: own-cell normalization matters; monotone weights do not identify different arity profiles.
- g3-ag-pair-continuation-20261025/JOINT-QUADRATIC-PREFIX-IDENTITY-CANDIDATE.md: exact source-jump integration by parts retains a signed reference mean and local source square.
- g3-ag-pair-continuation-20261025/storage-check/RESULT.md: existing bounded quadratic-storage resonance; changing the quadratic coefficients cannot silently eliminate the additional profile and reference forcing.
- g4-resumption-20261025/fair-multiscale-evidence/OCT7-BILINEAR-SOURCE.md: inherited exact projective top-band restrictions, actual bilinear contractions and full word 9-to-4 formula. Public supplier pin inherited in current G3 note: Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6, research/2026-10-07-dot-g4-exact-bilinear-source-reduction-0023z/EXACT-BILINEAR-REDUCTION-CANDIDATE.md. The local copy is titled Exact scalar reduction of the remaining 9-to-4 terms.

These are existing results, not rederived or re-attributed here. The present assessment reorganizes the exact remaining use-site; no corpus-complete novelty claim is made.

## 2. Exact product formula with all variable diagonals

Fix ONE frame for the entire word and ONE complete finite carrier. For the ordinary-return question use the ordinary Q spectral frame. For commutation with a fixed S(h), use that S(h) spectral frame. Do not diagonalize each cell in a different frame and omit the changes of basis.

Write the actual factor F_i=D_i+offdiagonal, with scalar root-count diagonal blocks d_a(i)I. Set

    F_i=(I+K_i)D_i,
    K_i(ab)=F_i(ab)/d_b(i),
    D_<i=product_(k<i)D_k,
    J_i=D_<i K_i D_<i^(-1).

Then EXACTLY

    W=(I+J_1)...(I+J_n)D_total.

All ordinary segments and cells are included in their actual chronology. The inherited adjacent-root-band vanishing is used here. In the ordinary frame it follows from projectivity; in the fixed-reference frame the ordinary-to-reference change has zero adjacent bands, preserving this property. Diagonal entries remain the actual no-merger d_a in either triangular frame.

For a=r, b=r-2, c=r-4 define rectangular blocks X_i=J_i(ab), Y_i=J_i(bc), Z_i=J_i(ac). Then

    W_ab/d_b(W)=sum_i X_i,
    W_bc/d_c(W)=sum_i Y_i,
    W_ac/d_c(W)=sum_i Z_i+sum_(i<j)X_i Y_j.             (1)

Only b can be a strict intermediate root count in the second expression: an intermediate r-1 or r-3 would require an adjacent block. More than two insertions cannot fit in a drop of four. Direct source Z_i is still present. Thus (1) is exact, not a perturbative two-merger truncation and not an assumption that source cells are ordinary gaps.

## 3. The conditional one-channel reduction

Suppose, as an EXTRA source adapter, there are fixed rectangular A,B and real scalars f_i such that

    K_i(ab)=f_i A,  K_i(bc)=f_i B.

Any fixed nonzero band constants can be absorbed into A,B. Let ell be a fixed linear functional on the ac block with ell(AB)=1. Define

    a_i=product_(k<i)d_a(k)/d_b(k),
    b_i=product_(k<i)d_b(k)/d_c(k),
    alpha_i=a_i f_i, beta_i=b_i f_i,
    t_i=b_i/a_i=product_(k<i)d_b(k)^2/[d_a(k)d_c(k)].

Then X_i=alpha_i A, Y_i=beta_i B and beta_i=t_i alpha_i. Actual log-concavity gives d_b(k)^2>=d_a(k)d_c(k) for equally spaced root counts, so t_i is nondecreasing. Positive ordinary factors make its increase strict across those factors: d_b²/(d_a d_c)=exp(4v) for spacing two and ordinary duration v. This exponent4 is NOT the adjacent-arity exponent2 in the earlier G4 note.

Define the exact local remainder

    delta_i=ell(Z_i)-(1/2)alpha_i beta_i.

For Q_j=sum_(i<=j)alpha_i, equation (1) becomes

    ell(W_ac/d_c(W))
      =(1/2)t_n Q_n²
        -(1/2)sum_(j<n)(t_(j+1)-t_j)Q_j²
        +sum_i delta_i.                                  (2)

This is just discrete integration by parts, with its endpoint term preserved. If the endpoint ab block vanishes, Q_n=0. If moreover sum delta_i<=0 and some positive t increment occurs at a nonzero Q_j, the right side is strictly negative. Such hypotheses would obstruct simultaneous endpoint ac zero.

But the one-channel relation and the sign of sum delta are EXTRA; neither is supplied by diagonal matching. Exact local half-product means ell(K_i(ac))=f_i²/2 because both sides acquire the same prefix diagonal a-to-c ratio. A finite actual source is not the same as one infinitesimal ordinary-gap insertion, so that identity is not automatic.

The homogeneous boundary theorem is the special case alpha_i=p_i rho^i, beta_i=p_i sigma^i, t_i=(sigma/rho)^i, delta_i=0 after the justified instantaneous projection and quadratic expansion. It does not prove these equalities for finite source factors.

## 4. Exact scalar profile-mismatch remainder

Even where the two blocks individually have fixed shapes, let instead

    X_i=alpha_i A, Y_i=beta_i B,
    beta_i=t_i alpha_i+e_i,
    delta_i=ell(Z_i)-(1/2)alpha_i beta_i,

using the SAME monotone diagonal t_i from Section3. No assumption of independent realizability of e_i is made. Algebra gives

    ell(W_ac/d_c(W))
      =(1/2)t_n Q_n²
        -(1/2)sum_(j<n)(t_(j+1)-t_j)Q_j²
        +sum_i e_i[Q_(i-1)+(1/2)alpha_i]
        +sum_i delta_i.                                  (3)

The extra term is a genuine chronological source-profile/prefix coupling. Knowing sum Y_i=0 imposes sum beta_i=0, not its sign or the sign of that mixed term. Nor does knowing all endpoint diagonals assign a sign to sum delta_i.

If X_i or Y_i varies in shape, choose fixed candidate A,B and retain matrix residuals E_i,F_i:

    X_i=alpha_i A+E_i, Y_i=beta_i B+F_i.

The ordered product has the ADDITIONAL exact remainder

    sum_(i<j) ell(alpha_i A F_j+beta_j E_i B+E_i F_j).    (4)

Consequently a projection does not remove all intermediate shape channels just because it removes one local tangent shape. Formulas (3),(4) identify the missing supplier rather than promoting a scalar free-profile quadratic to an actual source theorem.

In a single-band scalar description the uncontrolled own-cell ratio is visible directly:

    beta_i/alpha_i
       =[K_i(bc)/K_i(ab)]
         product_(k<i)d_b(k)^2/[d_a(k)d_c(k)].

Here the first quotient denotes scalar coefficients in fixed shapes, when such shapes exist; it may be undefined when the denominator vanishes. Only the product factor is controlled by log-concavity. A claim of common signed f_i must prove the own-cell quotient constant or otherwise control it on the full endpoint fibre. Across all arities a universal common-profile identity is already incompatible with the saved actual Dev4-zero/Dev5-nonzero controls; this is not a claimed counterexample for the particular12/10/8 block or for the whole endpoint fibre.

## 5. Existing ACTUAL-source obstruction, not an invented profile screen

The recovered Oct7 exact source reduction has a concrete additional profile. Its spectral d_n notation there is NOT the diagonal d_n in this note; call that spectral scalar c_n here. For an actual bare source B it defines

    e(B)=[2p7(3,2,1,1)-p7(4,1,1,1)]/6,
    S7(B)=-c6(B)/2+e(B).

It proves e generally nonzero by an explicit boundary polynomial evaluation and continuity to strict cells. No new endpoint-cell example is needed here. In its exact actual chronological formula,

    ell(e9 P9 W P4)
     =(15/2)sum_(i<j)A9(i)Z4(j)c9(B_i)
        { [M6(i,j)-M7(i,j)]c6(B_j)+2M7(i,j)e(B_j) }.   (5)

The A,Z,M are actual products of all intervening factor diagonals. Formula (5) is not identical to the drop-four channel (1); it is the older drop-five contraction. Its relevance is structural and exact: replacing the actual higher profile by its leading common jet omits the last term. The supplier explicitly says the negative-square sixth-order argument cannot simply be promoted to this full formula. This assessment preserves that warning and does not claim the residual proves a no-go for every possible whole-fibre inequality.

Likewise the old joint quadratic-prefix identity has source update a+=alpha*a-+x and ordinary forcing a'=15(a-A). Its square identity necessarily retains the signed mean15A integral(w a). The present e-prefix and local-delta terms are not eliminated by renaming that old affine coordinate as a homogeneous gap coefficient. The old storage-resonance calculation already explains why one bounded quadratic correction is insufficient; no new monomial ladder is proposed.

## 6. Distinct endpoint targets and precise missing gate

ORDINARY RETURN (G4 subclass): in the ordinary spectral frame an exact ordinary endpoint has all offdiagonal blocks zero. Thus (1) supplies sum X=0, sum Y=0, sum Z+ordered XY=0, while the endpoint diagonal constraints fix products d_r to the target pair exposure H. H is not automatically a separately fixed COMMON physical budget. To use (2) or (3), one still needs a source-valid bound on the exact profile/local/shape remainders conditioned on that SAME tuple and full diagonal fibre. Even a successful obstruction for this private subclass is not original finite natural-I forcing against all admitted rivals. Conversely one scalar zero is not a complete return.

G3 COMMUTATION: in a fixed reference S(h) spectral frame, complete commutation forces offdiagonal blocks between distinct root eigenvalues to vanish; within a repeated root block no spurious one-dimensional assumption is imposed. Paired clocks are separate exact constraints. The ordinary factor is generally NOT diagonal in this frame, so its X,Y,Z must remain in (1). Varying source diagonals do not commute with S(h) merely by being diagonal in another basis. The near-reference proof obtained delta/profile/shape control by first-velocity elimination and a second-order projection; it does not provide their nonlinear versions. Neither ordinary-return existence nor its failure is silently identified with G3 commutation.

A decisive new supplier would therefore be either (a) an exact fixed-channel identity plus nonpositive total local excess on the actual target fibre, or (b) a bound showing the sum of ALL terms (3),(4) is dominated by the displayed nonnegative prefix energy, with equality conditions strong enough for the intended target. Log-concavity supplies only the energy weights. The presently accepted source formulas do not supply (a) or (b). This route is paused at that precise mathematical adapter, not closed by a generic rank or freely selectable mixture argument.

## 7. Bounded check

check_adapter.py independently expands the exact scalar identity (3), including endpoint, profile and local remainders, with four fully symbolic positions. It also multiplies three symbolic triangular factors and verifies the diagonal-conjugation formula (1). PASS, using already-installed SymPy; no installation, numerical feasibility screen, source-parameter search or external agent contact. These are formal algebra controls, not evidence that arbitrary coefficients are physically realizable.
