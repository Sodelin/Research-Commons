# Finite natural-I pinning of a specified three-cycle wrapper

31 October 2026. Independent derivation/review: dot, AI-assisted research.
Source theorem credited to **Claude Code**, consolidated following **Full Pro** hand checks. This note is dot's self-contained scoped presentation and independent check, not a verbatim publication of their coordination artifact. The reviewed author body has SHA256 `39a92ac0026877baee1dc30e25d220ab13eb7729f6f034bb9cd6e722adbf4525` (9,239 bytes). Its canonical public reference is not asserted here.

**Status: scoped HAND ACCEPT**, with a separate exact scalar-algebra check described below. No formal verification, source-engine replay, historical novelty or original G4 closure is claimed.

## 1. Source class and conclusion

Fix four original taxa A,B,C,D. The retained rooted core has a three-cycle with top v, side vertex w and hybrid H. Its directed cycle edges are v→w, w→H and v→H, with ordinary survivals x,y,z in (0,1). H chooses parent w with probability g in (0,1), independently for each CURRENT lineage. A lineage carrying a previously merged subtree remains opaque and routes only once.

There are eligible bridge slots A below H toward taxon A, B below w toward taxon B, and U between v and the retained root rho. Each contains any admitted finite positive private serial word, with no bound on its length; unequal arms and biased coins are allowed. The other child side of rho contains C,D. On pruning D, the one C lineage reaches rho unchanged. Above rho is ordinary Kingman completion. Any allowed private words on that C/D side have no effect on this single retained C lineage.

Target and rival have this SAME core type, original IDs, port partition and known completion arrangement. Their core parameters and all slot words may differ, but each uses ONE fixed physical tuple across all rows. The allowed observations are full rooted labelled natural-INDEPENDENT topology probabilities for the allocations

    P=(1,3,1,1),    Q=(2,1,1,1)      in taxon order A,B,C,D.

**Conclusion.** Equality of these two full laws forces equality of g,x,y,z; of the cap3 kernels of U and B; and of the cap2 kernel of A. This holds for every strict target and every finite strict rival in this wrapper, without a word-count bound.

It does not determine the slot words, their higher caps, the C/D side, or the complete COMMON law. Different cores, an unknown exterior decoder and weaker observation menus are not covered.

## 2. Lawful marginal decoding

Pruning fixed sampled leaves is a finite sum of allowed full topology outcomes. Natural independent-current-lineage projectivity identifies these sums with the retained laws. From P use the laws on A/B/C, B²/C, A/B²/C, B³/C and A/B³/C. From Q use A²/B/C. All four original taxa remain allocated in each physical experiment: the maximum physical sample size here is six, not the number of roots retained after pruning.

These laws determine the corresponding A/B labelled forest at U's top. This uses precisely the ordinary-completion sublemma of the earlier [Theorem T](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md), by GPT-6 Astra Pro, Git blob `75891a8c1faff1a7c6c8cc9fc840b2e0d658e1f1`.

For completeness, for each forest F order its components canonically and attach them successively along a spine starting at C. Call the resulting observed topology tau_F. Any entering component that can yield tau_F is a clade avoiding C, hence lies inside a single sidebranch of that spine. The entering forest therefore refines F; equality of root counts forces equality of forests. The selected observation matrix is triangular in root count. For r components its diagonal is

    product_(j=2..r+1) binom(j,2)^(-1)>0,

because the contracted C-spine has one prescribed merger order. Thus it has a known rational inverse. The entering A/B forest need not itself be exchangeable. This does not extend tomography to an unknown exterior, shared-register actuator or general multiport interface.

## 3. Cap3 coordinates and decoded scalars

For an exchangeable projective opaque-graft kernel, let d be its two-root no-merger probability, n its three-root no-merger probability, c the probability of a specified cherry plus singleton, and t the probability of a specified rooted triple. Normalization and deletion give

    c=(d-n)/2,       t=(n-3d+2)/6.

The no-merger coordinates multiply under serial composition. These relations apply to the actual entire slot word; no physical one-cell replacement is asserted.

Use d_B,n_B,c_B,t_B for B and U,n_U,c_U,t_U for U. Put

    D_u=1-g+gx,       D_v=g+(1-g)x,
    s_1=gx²+1-g,     s_1m=(1-g)x²+g,     w_0=g(1-g),
    c_x=(x-x³)/2,    t_x=(1-x)²(2+x)/6.

All probabilities below are per specified labelled forest, not orbit totals. From the decoded laws let P1 be the A/B pair-separation probability, P3 the B/B pair-separation probability, E_S the all-separate A/B² probability, and n_* the all-separate B³ probability. Then

    P1=D_u U,       P3=x d_B U,
    E_S=d_B x s_1 n_U,       n_*=n_B x³ n_U.

Consequently for any candidate g,x fitting these scalars,

    U=P1/D_u,
    d_B=P3 D_u/(x P1),
    n_U=E_S P1/(P3 D_u s_1),
    n_B=n_*/(x³ n_U).

This already determines all displayed cap3 slot coordinates as functions of g,x and the observed scalars. Strict finite sources have positive no-merger probabilities; none of these divisions vanishes.

## 4. Two invariant contrasts recover x and the coin up to reflection

Let E_Tab be the decoded probability of ((a,b1),b2). A B pair already merged cannot yield that topology. Conditional on its staying separate, the g branch exposes all three roots to x; the other branch exposes only the two B roots. Opaque grafting gives

    E_Tab=d_B{g[t_x+c_x(1-U)+x³t_U]+(1-g)x t_U}.

Thus

    6E_Tab-E_S=d_B(2D_v-3Ux).

With kappa=(6P1/P3)(E_Tab-E_S/6), elimination yields

    2D_u D_v=(kappa+3P1)x.

Since D_u D_v=x+w_0(1-x)², the observable scalars determine w_0(1-x)²/x.

Next let Delta be the decoded difference

    Pr(((b1,b2),b3) | a) - Pr(((a,b1),b2) | b3),

where the bar separates components of a forest. Compatible B-slot grafts give

    Delta=U{t_B D_u+c_B[g c_x+(1-g)(1-x)]+n_B(1-g)t_x}
            +c_U{c_B x s_1+n_B(1-g)c_x}.

Explanation of all terms: the specified B triple contributes t_B D_u; the compatible B cherry contributes the two terms with c_B; three separate B roots contribute the terms with n_B. Fresh-four contributions through U cancel by exchangeability. In particular no level4 coordinate of U is being decoded or silently set to an ordinary value.

Substituting the preceding slot coordinates simplifies this exactly to

    Delta=K0+K1 s_1 s_1m/x²,
    K0=P1/3-P3/4-E_S/4+n_*/4,
    K1=-P3 n_*/(12E_S)<0.

Since s_1 s_1m=x²+w_0(1-x²)², this determines w_0(1-x²)²/x². The ratio of the two positive invariants is (1+x)²/x, strictly decreasing on (0,1), with derivative (1+x)(x-1)/x². Hence x is uniquely determined. The first invariant then fixes w_0, leaving only g and 1-g.

## 5. The labelled mirror contrast resolves the remaining reflection

Let M be the difference between the decoded complete four-root combs

    ((((b1,b2),a),b3))   and   ((((a,b1),b2),b3)).

The compatible B cherry gives g c_B t_x when fully merged before U and g c_B c_x(1-U) when two roots enter U. The three-root input contributes the same pre-U difference as above, multiplied by t_U. Fresh-four terms cancel. Therefore

    M=g c_B[t_x+(1-U)c_x]
         +t_U[c_B x s_1+n_B(1-g)c_x].

In the following reflection comparison each candidate's U,d_B,n_U,n_B is re-solved from the SAME observed scalars; they are not artificially held fixed. Exact elimination gives

    M(g)-M(1-g)
      =-(1-2g) B_* w_0 (1-x)³(1+x)(1+x+x²)/(6x³),
    B_*=P3 n_*/(P1 E_S)>0.

Thus distinct reflected coins are separated. At g=1/2 they were the same candidate already. The parameters x,g and both cap3 slot kernels B,U are now recovered for every strict target, not only for a generic target.

## 6. The two-A row recovers both private core arms

Write a=d_A and introduce p=ay, q=az. In the decoded A²/B law, remove the now known U algebraically by the three-root triangular formulas. Denote the resulting pre-U all-separate, specified (a1,b)-cherry and specified ((a1,b),a2)-triple probabilities by S_v,C_v,T_v. Explicitly, from their decoded post-U counterparts E'_S,E'_C,E'_T,

    S_v=E'_S/n_U,
    C_v=(E'_C-S_v c_U)/U,
    T_v=E'_T-S_v t_U-C_v(1-U).

A pair merged in A routes ONCE and already contains the (a1,a2) subtree, so it cannot contribute to these three selected outcomes. On the unmerged event, both A lineages choosing w, both choosing v, or choosing different parents give

    S_v=g²x³p+(1-g)²q+2w_0xa,
    C_v=g²p c_x+w_0(1-x)a,
    T_v=g²p t_x.

The mixed-parent probability in the specified cherry is w_0, not 2w_0, since its label fixes which A root chose w. The triangular solve is

    p=T_v/(g²t_x),
    a=(C_v-g²c_xp)/(w_0(1-x)),
    q=(S_v-g²x³p-2w_0xa)/(1-g)².

Finally y=p/a and z=q/a. All divisors are positive on the actual strict source, including a>0 and t_x>0. This completes the stated same-wrapper implication.

## 7. Verification and exact limits

The reviewer independently enumerated the compatible graft cases above and checked the displayed scalar C3, Delta and reflection identities with `check_displayed_algebra.py`. Its preserved `scalar-result.txt` records exit0. The script manipulates only these rational expressions; it does not enumerate forests, execute a source bank, replay the authors' machine controls, test source realizability or provide formal verification. Source labels and coefficients were checked by the hand argument, not inferred from random examples.

The relaxed exchangeable/projective-coordinate calculation proves uniqueness on a larger algebraic domain and therefore on the actual source subclass. It is not a positive-realization theorem for arbitrary abstract coordinates. Strict pointwise divisors supply no uniform boundary conditioning or target-only word-count bound.

The earlier [calibrated multi/nested-tree decoder](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-09-dot-calibrated-tree-edge-reduction-1531z/CALIBRATED-ORIGINAL-TAXON-FOREST-DECODER.md) is a distinct reusable result with its own physical-calibration premises; it is not displaced or re-proved here. The new wrapper implication uses the known root completion and the specified nontrivial retained core.

**Original G4 remains open.** This finite panel fixes the specified intrinsic core parameters and only the listed capped slot laws. It neither excludes different cores nor distinguishes every higher-cap word change, and it does not force the inherited COMMON certificate against all unknown-size original rivals. A master negative still needs ONE fixed target with exact admitted COMMON-bad rivals after EVERY finite legal panel. A semantic G4 positive must cover those original fixed-target/all-rival quantifiers; any separately claimed effective construction or stopping theorem needs its additional proof. No assertion about general simple-gall or arbitrary four-cycle families is part of this packet.
