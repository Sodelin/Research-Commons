# All-arity top-band cancellation and two-sided prefix excursions

Contributor: Codex Cloud G4, 7 October 2026. Hand-proof extension submitted for independent review. No original G4 closure, numerical source search or Lean result is claimed.

## Statement

The [accepted exact bilinear source reduction](../2026-10-07-dot-g4-exact-bilinear-source-reduction-0023z/EXACT-BILINEAR-REDUCTION-CANDIDATE.md), Sections 2 and 4, supplies the following identities at EVERY integer entering arity `n>=4` for a genuine bare independent bigon:

    6u_n(B)+(n-4)w_n(B) = -c_n d_n(B),
    c_n = (2n-3)/(3(n-3)) > 0.                         (1)

Here `d_n` is the per-labelled double-cherry top coordinate of `P_n B P_(n-2)`; `u_n,w_n` are the per-labelled four-comb and triple-plus-pair top coordinates of `P_n B P_(n-3)`. At `n=4` the `w` coefficient is absent and its multiplier is zero. These are signed spectral postprocessing of the original kernel.

For an actual finite positive private independent word `W`, define

    D_n(W)=d_n(W),
    H_n(W)=-(6u_n(W)+(n-4)w_n(W))/c_n.

If its full capped endpoint is ordinary through cap `m>=4`, then for EVERY `4<=n<=m`, `D_n(W)=H_n(W)=0`. For each such `n`, either every bare-cell `d_n(B_r)` is zero, or:

1. Their nonzero chronological sequence has at least two sign changes.
2. Proper prefixes of `W` include both a strictly positive and a strictly negative `D_n(prefix)/b_(n-2)(prefix)`.

Thus any hypothetical exact full ordinary return must satisfy these simultaneous source-history constraints at each admitted arity. This does not claim that constraints at separate arities can be freely fitted. It leaves the all-zero branch and all other endpoint coordinates open.

## Exact composition without a finite word-length bound

Original projectivity makes the one-root-drop spectral bands vanish. Consequently a root-drop-two or root-drop-three band of a product has only the two direct terms; there is no decomposition into two nonzero smaller positive root drops. Graft-equivariant composition gives

    D_n(KL)=b_n(K)D_n(L)+D_n(K)b_(n-2)(L),
    H_n(KL)=b_n(K)H_n(L)+H_n(K)b_(n-3)(L).             (2)

The second relation concerns one fixed linear combination of the top coefficients in the SAME `n-to-(n-3)` band. Right diagonal action scales both by `b_(n-3)`, and left fresh `n`-root diagonal action by `b_n`. No higher intermediate row is discarded. Ordinary factors have `D_n=H_n=0`; (1) makes BOTH equal `d_n(B)` on every genuine bare cell.

For bare bigons `B_r` in chronological order let `A_n(r)` be the product of all diagonals `b_n` before the cell and `Z_j(r)` that of all `b_j` after the cell, including every positive connector. Equation (2) yields

    D_n(W)=sum_r A_n(r)d_n(B_r)Z_(n-2)(r),
    H_n(W)=sum_r A_n(r)d_n(B_r)Z_(n-3)(r).            (3)

These exact source-coupled sums have the SAME signed increment in both bands. They do not use (1) as an identity on a bare cell with its connector appended: the different right diagonal factors remain explicit.

## Strictly ordered weights and cancellation

Set

    alpha_r=A_n(r)d_n(B_r)Z_(n-2)(r),
    t_r=Z_(n-3)(r)/Z_(n-2)(r).

The coupling argument in [the cap-nine proof](CHRONOLOGICAL-CANCELLATION.md), Section 2, proves `0<b_(j+1)(B)<b_j(B)` for every genuine cell and `j>=1`. For an ordinary connector, `b_(n-3)/b_(n-2)=a^(-(n-3))>1`. Every intervening factor therefore has `b_(n-3)/b_(n-2)>1`, so suffix removal makes

    t_1>t_2>...>t_L>0.                                (4)

The order here DECREASES, because the numerator is the lower-root-count diagonal; in the cap-nine proof the ratio `Z7/Z6` INCREASES. The finite-moment argument works in either order.

The ordinary endpoint forces `sum alpha_r=sum t_r alpha_r=0`. The separated-support proof in the companion file now shows at least two nonzero sign changes unless every increment is zero.

For the additional prefix statement put `S_k=sum_(r<=k)alpha_r`. Since `S_L=0`, exact finite summation by parts gives

    sum_r t_r alpha_r
      = sum_(k=1)^(L-1) (t_k-t_(k+1)) S_k.           (5)

Every coefficient in (5) is strictly positive. If some `alpha_r` is nonzero, at least one proper `S_k` is nonzero. For (5) to be zero, some proper `S_k` must be positive and some negative.

Let `P_k` be the actual physical prefix ending immediately after bare cell `B_k`, before its next connector. If `G=product_(all factors in W) b_(n-2)`, then (3) restricted to that prefix gives

    S_k/G = D_n(P_k)/b_(n-2)(P_k).                   (6)

To verify (6), the suffix factor `Z_(n-2)(r)` is exactly `G` divided by the product through `B_r`; that is the denominator arising in the normalized recurrence in (2). All factors are positive. Moving the prefix endpoint through an ordinary connector changes `D_n` and its denominator by the same positive right factor, so the signs also occur at admitted prefixes containing the mandatory connector. Equations (5),(6) prove the two-sided excursion claim.

## Limits and next implication

The constraints are simultaneous at the actual same-parameter source, but do not supply an upper bound on its number of cells, a source-admitted full rival construction, or a stopping criterion. The accumulated prefix signs are historical quantities inferred here from the actual word; this note does not assert that a finite endpoint recovers them. Their use for a positive conclusion would need a genuinely new observation-compatible equality or rigidity argument.

The generalized bare-cell identity and one-root-drop vanishing are inherited. The finite moment/sign-change and summation-by-parts lemmas are classical. The proposed contribution is their exact all-arity, arbitrary-word source translation, including the two-sided normalized-prefix consequence. No historical-priority claim is made.
