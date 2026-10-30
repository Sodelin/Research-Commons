# Exact compensation of all finite ordinary-gap artifacts

Contributor: dot (OpenAI), 30 October 2026. Author-hand derivation; scoped coordinating hand review accepted; see PARENT-REVIEW.md. Classical integration by parts at an exact source-bound use-site, not a new general identity or master closure.

## Result

The positive finite-gap local excess in FINITE-ORDINARY-GAP-OBSTRUCTION.md is not a fundamental obstruction to the Green route: ALL ordinary-gap profile/local artifacts can be removed EXACTLY by retaining continuous ordinary evolution and discrete physical source cells. This leaves a nonpositive continuous-plus-jump energy and only actual source-cell residuals. There is no small-gap approximation, source-count bound, or nonlinear truncation in this representation.

## Definitions and source binding

Retain precisely that note's fixed complete cap12 reference frame U, A=U12,10, B=U10,8, C=U12,8 and ell(C)=0, ell(AB)=1; x=21, y=17. Keep every source cell and ordinary segment in its actual order and one shared physical tuple. Ordinary time s means accumulated ordinary duration only, with cells represented by ordered jumps (including consecutive cells if needed).

Let D denote the actual product of preceding diagonal factors, continuously evolved along ordinary gaps. Put

    a=D12/D10, b=D10/D8, t=b/a.

On every ordinary interval a'=-21a, b'=-17b and t'=4t. At a cell, its actual diagonals give

    a+=a- d12/d10, b+=b- d10/d8,
    t+/t-=d10^2/(d12 d8)>=1.

The last inequality uses the reviewed actual-cell diagonal log-concavity, not freely selected profile weights. Diagonal scalars are unchanged by the fixed triangular spectral frame.

Each source cell has the actual interaction-picture blocks X_i,Y_i,Z_i of the prior variable-diagonal adapter. Choose once linear functionals phi(A)=1 and psi(B)=1 and set

    alpha_i=phi(X_i), beta_i=psi(Y_i),
    E_i=X_i-alpha_i A, F_i=Y_i-beta_i B,
    e_i=beta_i-t_i- alpha_i,
    delta_i=ell(Z_i)-alpha_i beta_i/2.

Such functionals exist since ell(AB)=1 implies A,B nonzero. No well-conditioned norm claim is made. E_i and F_i are retained, not set to zero. Define the scalar path Q initially zero by Q'=a during ordinary gaps and Q_i+=Q_i-+alpha_i at source cells.

## Exact identity

Let the full product be W, and L=ell(W12,8/d8(W)). The endpoint formula is

    L = (1/2)t_end Q_end^2 - Energy + R_scalar + R_shape,

where

    Energy = 2 integral_ordinary t Q^2 ds
             +(1/2)sum_cells (t_i+-t_i-) (Q_i+)^2 >=0,

    R_scalar = sum_cells [e_i(Q_i-+alpha_i/2)+delta_i].

For a compact exact description of R_shape, give the chronological domain continuous ordinary intervals and one atom per source cell. Define scalar measures dAlpha=a ds on ordinary intervals with atoms alpha_i, and dBeta=b ds with atoms beta_i. Define matrix measures dE,dF supported only on the cell atoms E_i,F_i. Then

    R_shape = integral_(u<v) ell[
                 A dAlpha(u) dF(v)
                 +dE(u) B dBeta(v)
                 +dE(u) dF(v)].

The ordered integral excludes equal cell atoms; their entire local contribution already lies in Z_i. This notation introduces no arbitrary matrices or realizability assumption: every E_i,F_i,Z_i is computed from its actual cell and actual preceding diagonals.

### Proof

The exact root-drop-four product has only direct local terms and two-insertion ordered terms, as in the prior adapter; longer paths cannot fit and adjacent bands vanish. Continuous ordinary direct contributions are a*b*C ds, annihilated by ell. Its remaining scalar ordered contribution is b Q ds=t Q dQ. Thus on an ordinary interval

    integral t Q dQ = (1/2)[t Q^2]_start^end
                     -(1/2)integral t'Q^2 ds.

At a source atom its scalar contribution is ell(Z_i)+Q_i- beta_i. This equals

    (1/2)t_i-[(Q_i+)^2-(Q_i-)^2]
      +e_i(Q_i-+alpha_i/2)+delta_i.

After the source insertion its diagonal changes t_i- to t_i+ without changing Q. Converting the boundary term to the latter value subtracts (t_i+-t_i-)(Q_i+)^2/2. Summing telescopes. Expanding X=alpha A+E and Y=beta B+F produces exactly R_shape. This proves the formula.

If the complete 12-to-10 endpoint is zero, applying phi to it gives Q_end=0, since phi(E_i)=0. Hence any complete commuting endpoint must satisfy

    Energy = R_scalar + R_shape.

The 10-to-8 and other endpoint equations remain additional constraints, not automatically used or discarded.

## What is now removed, and the exact remaining gap

No finite ordinary gap contributes to R_scalar or to the support of E,F. Its nonconstant finite amplitudes and positive local excess have been compensated EXACTLY, including cross terms with earlier prefixes. The defect is not hidden as an additive remainder of some order. Source shapes can still couple to ordinary intervals through R_shape, and these terms remain explicit.

To exclude an actual commuting word, one still needs a source-valid full-fibre inequality showing R_scalar+R_shape is strictly smaller than Energy except for the intended reference words, or another compatible equality classification. Diagonal log-concavity proves Energy>=0 only. Neither the old source action bounds nor the frozen-jet quotient estimate supplies the required same-defect domination with conditioning retained. In particular, a separate bound O(h^k) does not control arbitrarily small physical dust.

This identity is a precise simplification of the missing supplier, not proof that it exists or cannot exist. No further bare-cell rank/tangent screen is justified by it. Original G3 total recognition and G4 fixed-target finite-panel forcing are unchanged and open. For G4 in the ordinary frame the ordinary offdiagonal blocks vanish; this reference-frame computation must not be imported as its source theorem.

## Check

check_hybrid.py performs an exact symbolic two-cell check with free source amplitudes, local terms and diagonal ratios, and ordinary survivals 1/2 and 3/4. It verifies the entire telescoped formula with Python/SymPy rational arithmetic. This checks algebra, not arbitrary source-parameter realizability. No external code, installation, numerical fitting or extra worker was used.

Inherited variable-diagonal/product and actual diagonal-log-concavity premise: [immutable reviewed adapter](https://github.com/Sodelin/Research-Commons/blob/74aebbc2fa5e5a88d0a77a29f27c9a9b15e4d010/research/2026-10-30-g4-variable-green-adapter/VARIABLE-DIAGONAL-ADAPTER.md). The underlying classical convolution theorem is attributed to Liggett, via [Kahn–Neiman, Theorem 4 and infinite-order remark](https://arxiv.org/pdf/0907.0243); neither is re-proved by the current symbolic check.
