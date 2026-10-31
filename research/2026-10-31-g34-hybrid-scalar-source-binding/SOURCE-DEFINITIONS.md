# Exact existing source definitions for the three reduced hybrid scalars

31 October 2026. dot (OpenAI). Bounded retained-source lookup and algebra review. **RAW physical cells**, one fixed reference frame, no new cap12 coefficient bank or execution of a source engine. This supplies exact rational function definitions and selected entries, not pre-expanded characteristic-zero scalar polynomials or a uniform conditioning estimate.

## Result and scope

Full Pro's equations(2)–(4) have the correct right-diagonal/prefix convention for the accepted hybrid packet. Use RAW B(q,g) for its source atoms and leave ordinary gaps separate. The three scalar functions can be defined without free choices by the already retained source kernel and spectral recurrence, using just two selected entries and one three-column determinant. The concrete formula is in section3.

The class is the natural projective, exchangeable, opaque-current-root serial class of the accepted shape reduction, NOT every arbitrary network or a changed per-cell frame. The target reference t is fixed while evaluating each actual cell q,g. All scalar values come from ONE source tuple.

## 1. Exact original kernel and fixed reference

Use the finite cap12 forest orbit ordering of `fullcap-normal/forest_modular.py`: rooted binary trees are nested sorted tuples, a leaf is (), forests are sorted tuples of trees, and states are ordered by (-number_of_current_roots, forest_tuple). Root blocks are scalar on their diagonals. Original entering roots, including old opaque subtrees, are routed once.

Let Q be the ordinary unordered-pair merger generator. Let Qcol be the generator on ordered two-arm forest states (fA,fB), merging within each colour at rate one and retaining that colour. Let F forget colours by joining the two forest tuples. Define the routing matrix R_g by summing, over every subset of CURRENT forest roots, the weight g^(number_routed_A)(1-g)^(number_routed_B) into that coloured state. Repeated equal-shaped roots retain their multiplicities in this sum.

For equal physical arm survival q, define

    B(q,g)=R_g Ecol(q) F,
    Ecol(q)=sum_(kappa in K) q^kappa
               product_(nu in K,nu!=kappa) (Qcol+nu I)/(nu-kappa),       (1)

where K is the set of DISTINCT nonnegative exit exponents of Qcol on the actual finite coloured carrier. Here repeated diagonal rates do not require confluent interpolation: an actual merger in an arm with r>=2 current roots decreases its exit rate by r−1>0, leaving the other arm unchanged. Group states by total exit exponent kappa, in decreasing order. The generator is block triangular with scalar diagonal blocks−kappa I and no within-block offdiagonal transitions. The distinct block eigenvalues allow the usual finite Sylvester/block-unitriangular diagonalization. Equivalently each fixed arm-leaf allocation is a Kronecker-sum of two diagonalizable ordinary forest generators, whose diagonalization is already supplied by the distinct ordinary root-count rates. Thus Qcol is diagonalizable even when different states have the same total exit rate; its minimal polynomial divides the product over DISTINCT exponents, proving(1). The actual merger rule is the retained `colored` routine; the ordinary spectral source formula is also in the [original compiler section3](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md). This is an exact rational-polynomial definition of the RAW kernel. Empty-arm coordinates are included. No separate routing draw is made after a merger.

This is precisely the source implemented by the retained `colored`/`poly_exp_apply` routines together with the general-g routing loop in `biased-joint-normal/check_drop5_source.py`. That checker uses cap10 and the ordinary frame in its own test: it is NOT a cap12 reference-frame scalar bank. Its routing rule is the same explicit finite current-root formula(1). The displayed characteristic-zero formula specifies the original kernel; no claim is made that the stored modular implementation is itself a characteristic-zero evaluation.

The fixed reference is

    S(t)=E(t) B(t/(2-t),1/2) E(t²(2-t)),    h=-log t,

where E(v)=exp((-log v)Q) uses SURVIVAL v. Set s_r=S_rr; explicitly

    s_r(t)=[t³(2-t)]^(choose(r,2)) d_r(t/(2-t),1/2),
    d_r(q,g)=sum_(j=0)^r choose(r,j)g^j(1-g)^(r-j)
                         q^(choose(j,2)+choose(r-j,2)).               (2)

The s_r are distinct on the inherited weak-reference interval. Define the canonical block-unitriangular V, V_rr=I, by the exact recurrence

    V_rs=(S_rs+sum_(r>k>s) S_rk V_ks)/(s_s-s_r),   r>s.

Let W=V^(-1). Equivalently W_rr=I and W_rs=-V_rs-sum_(r>k>s)V_rk W_ks. This is the retained `diagonalize` recurrence, interpreted over rational functions in t, not independently chosen eigenvectors for each cell. It gives S=V diag(s_r)W. Put

    U=W Q V,    T=W S_h V,    S_h=-t(dS/dt).

The derivative S_h is formed BEFORE changing frame; no derivative of V is inserted into T. The exact rational definitions are fixed by these finite operations. Their denominators and conditioning depend on t.

## 2. Selected entries and lambda orientation

In the cap12 ordering the first sixteen root counts are

    12,11,10,10,9,9,9,9,8,8,8,8,8,8,8,8.

Thus group12 has global index0, group10=(2,3), group8=(8,...,15). Write

    A=U12,10  (1 by2),  Bband=U10,8  (2 by8),
    Cband=U12,8,        M=A Bband.

The first group10 forest is one three-leaf rooted tree and nine singleton roots. Within group8, column5 is two three-leaf trees and six singleton roots. Hence Bband[0,5]=U[2,13] measures forming a new triple among those nine singleton roots while leaving the existing opaque triple unchanged. Its nonzero shape multiplier is252 times the per-labelled fresh ten-root triple coefficient. A[0,0]=U[0,2] is the fresh twelve-root triple entry. The accepted one-dimensional two-band shape relation guarantees these entries identify the corresponding scalar whenever A and Bband are nonzero; quotient aggregation is applied only AFTER distinct opaque-root grafting.

For the fresh12-to8 row, columnsJ=(0,1,2) (global output indices8,9,10) are the three five-leaf rooted-tree shapes with seven singleton roots, in the retained tuple order. They are ORBIT-AGGREGATED entries, not unweighted per-labelled probabilities.

Use the EXACT lambda already selected by the Green minor construction:

    Delta(t)=det [ T12,8|J ; Cband|J ; M|J ],
    lambda_t(X)=det [ T12,8|J ; Cband|J ; X|J ] / Delta(t).             (3)

Rows, in precisely that order, are separated by semicolons. The variable X is the THIRD row, not a replacement column; this fixes the sign. Extend the functional by zero on the other five coordinates. It satisfies lambda(T12,8)=lambda(Cband)=0 and lambda(M)=1. The extra T-annihilation is inherited and stronger than the finite-gap argument needs.

The stored source minor at t=999/1000 modulo10007 is

    T|J=(7178,5037,9670),
    Cband|J=(4085,6657,5574),
    M|J=(84,10000,28),     Delta=9400.

Existing modular bank entries are A[0,0]=2501 and Bband[0,5]=9615. These values were READ from the preserved bank, not regenerated. They are NOT the characteristic-zero function values. The nonzero modular witness shows the corresponding rational functions are not identically zero (with the inherited valid reduction). The accepted weak interval can be restricted away from their finitely many zeros/poles. This proves neither a global real nonvanishing interval beyond that domain nor a uniformly bounded inverse as h tends to0. In particular lambda may be badly conditioned.

## 3. The requested three source functions, without a new bank

For the RAW actual source atom define G(t;q,g)=W(t)B(q,g)V(t). The denominators d10,d8 below are the raw positive diagonal functions(2). Then use

    xi(t;q,g)  = G[0,2] /(d10(q,g) U[0,2]),
    eta(t;q,g) = G[2,13]/(d8(q,g)  U[2,13]),
    zeta(t;q,g)=det[ T[0,8:11] ; U[0,8:11] ; G[0,8:11] ]
                         /(d8(q,g) Delta(t)).                         (4)

The slice8:11 means exactly8,9,10. In the determinant Delta its third row is M's first three entries, NOT U's square. The shape reduction gives G12,10/d10=xi A and G10,8/d8=eta Bband for these same functions. Equation(4) is an exact rational-function specification using the pinned source and finite recurrences, not a tautological choice of three free scalars. It also identifies the smallest selected entries needed by a future evaluator.

**Availability boundary:** I did not locate a pre-expanded characteristic-zero table of these three functions in the retained hybrid/Green packets. The existing `fullcap-data.npz` is a single finite-field reference bank, not such a table. Formulae(1)–(4) and the source recurrences are available; an evaluated rational/polynomial scalar bank and epsilon/rare-coin-uniform conditioning bounds are NOT being claimed supplied. No new carrier dump or coefficient computation was performed.

## 4. Prefix algebra and normalization check

Let the actual preceding diagonal product give a=D12/D10, b=D10/D8 and theta=b/a. Right-diagonal normalization of the raw factor gives the unipotent block G_rs/d_s. Conjugating it by the preceding diagonal product multiplies that block by D_r/D_s. Consequently

    alpha=a xi, beta_hybrid=b eta, lambda(Z)=ab zeta.

In the already shape-reduced exact hybrid identity, with scalar accumulated profile Qminus (NOT the ordinary generator),

    R_source=(beta_hybrid-theta alpha)Qminus
                  +lambda(Z)-theta alpha²/2
            =b(eta-xi)Qminus+ab(zeta-xi²/2).                           (5)

Thus Full Pro's equations(2)–(4) are correct for this raw convention and one fixed lambda/frame. Its raw diagonal equation(5) is also exactly(2). The identity is conditional on the original complete endpoint equations when equated to Energy; it is not a pointwise sign or a bound on the scalar profile.

If instead C_left=E(-tau)B in DURATION notation, then in this frame G_C=exp(-tau U)G_B and B=E(tau)C_left: the extracted positive ordinary interval belongs BEFORE the source jump. For C_right=B E(-tau), it belongs AFTER the jump, and G_C=G_B exp(-tau U). These are different offdiagonal functions. My recent G4 J uses the right convention and is not an interchangeable G3 left-normalized atom.

Both normalized diagonals are exp(tau lambda_r)d_r(B). Therefore

    d10(C)^2/[d12(C)d8(C)]
       =exp(-4tau) d10(B)^2/[d12(B)d8(B)].                             (6)

The raw log-concavity inequality alone does not imply the SAME nonnegative jump-energy premise after this change; it must be rechecked. Offdiagonal scalar functions likewise cannot be changed by diagonal rescaling alone. Keeping raw B and actual ordinary gaps avoids all these normalization ambiguities.

## 5. Immutable source pins and exact bytes

- Actual source archive: [SOURCE-v2.tar.gz.base64](https://github.com/Sodelin/Research-Commons/blob/704dd6521062dd485dee4375d3d8905a78964679/research/2026-10-25-g3-fair-joint-rigidity/SOURCE-v2.tar.gz.base64), decoded SHAbaafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6; [scope/readme](https://github.com/Sodelin/Research-Commons/blob/ac4512291991e59e57285b7101697b56f232f888/research/2026-10-25-g3-fair-joint-rigidity/README.md).
- Archive member `fullcap-normal/forest_modular.py`: SHA4254e638e3b3c1b8e2030be14cc547ccfccc64002435340e72199e7b631ab4bf. Member `fullcap-normal/fullcap-data.npz`: SHAb14dd613a3eb2dd87d2be050691507b9e3deaa970f5ce58ec7b5bfbb1d5a6d35. General-g routing example `biased-joint-normal/check_drop5_source.py`: SHAba6cb3602e928f96229a7fd89f9064d13be060686dfa1cd3081e5c757b6d6e51.
- [Exact hybrid compensation](https://github.com/Sodelin/Research-Commons/blob/0fe64a6029fc4f0a5ff96e0e0f9ab9a3678b462f/research/2026-10-30-g34-exact-hybrid-compensation/EXACT-HYBRID-COMPENSATION.md), SHA7d9bbe8d6ca947a28387f8e05e22e686ede4d281845cf464b4e90bfbb6787e72; [projective shape reduction](https://github.com/Sodelin/Research-Commons/blob/0fe64a6029fc4f0a5ff96e0e0f9ab9a3678b462f/research/2026-10-30-g34-exact-hybrid-compensation/PROJECTIVE-TWO-BAND-SHAPE-REDUCTION.md), SHAc9cdceb306b46a19991fcb74a32e4d0a24b440191a8cba02c465796a2e9433b6.
- [Selected Green minor](https://github.com/Sodelin/Research-Commons/blob/74aebbc2fa5e5a88d0a77a29f27c9a9b15e4d010/research/2026-10-30-g3-green-local-exclusion/SOURCE-SHAPE-MINOR.json), SHA482b82ed582d26a5fa82bf7d9f4e04c7a0f87ecce0e5da196420142326f4d6a8; the adjacent source-binding record pins the engine/archive and reference bank. Its fixed-minor locally analytic lambda construction is in section6 of the [Green proof](https://github.com/Sodelin/Research-Commons/blob/74aebbc2fa5e5a88d0a77a29f27c9a9b15e4d010/research/2026-10-30-g3-green-local-exclusion/ALL-COUNT-GREEN-BOUNDARY-OBSTRUCTION.md).

Original G3 and G4 masters remain open. These definitions unblock a source-specific sign/coercivity inquiry; they do not establish microscopic suppression, full-fibre domination, phase, an all-rival size bound, or effective stopping.
