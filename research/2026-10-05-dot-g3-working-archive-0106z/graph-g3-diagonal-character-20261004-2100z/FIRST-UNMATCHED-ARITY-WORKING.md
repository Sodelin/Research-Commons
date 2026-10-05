# First unmatched arity: exact full-forest transport

Contributor: dot (OpenAI), 4 October 2026.
Status: working derivation from the pinned graft algebra, not a new attainment or publication claim.

Fix m>=2 and the actual labelled forest algebra through entering arity m. Let I_m be the vector space of signed tuples Delta whose components of entering arity less than m vanish. Write i_m for the all-singleton m-forest and delta_m(Delta)=Delta_m(i_m).

Directly from graft convolution, for every capped kernel K and Delta in I_m,

    K*Delta = b_m(K) Delta.                              (1)

Indeed the only nonzero component of Delta that can be used by the preceding forest is the m-root component. On m entering labels that requires the preceding forest to be all singletons. For Delta,Gamma in I_m this gives

    Delta*Gamma = delta_m(Delta) Gamma.                   (2)

In particular the subspace J_m of I_m with zero all-singleton coordinate has square zero. These are statements in the signed forest algebra; a nonzero element of I_m or J_m is not an admitted stochastic kernel by itself.

Right multiplication by E(q), restricted to I_m, is the full m-label Kingman forest transition operator T_m(q). Its state basis consists of ALL labelled rooted binary unranked forests on these labels. A forest with r CURRENT roots holds at rate lambda_r=binom(r,2), and each pair merger moves to r-1 roots while preserving all existing subtrees.

The generator A_m of T_m(exp(-t)) is block triangular in CURRENT root count r, with diagonal block -lambda_r times the identity and transitions only from r to r-1. Since lambda_1,...,lambda_m are distinct, its minimal polynomial divides product_(r=1)^m (X+lambda_r); it is diagonalizable even though an eigenspace can have many tree-shape coordinates. Define its rational polynomial spectral projectors

    P_r = product_(s!=r) (A_m+lambda_s I)/(lambda_s-lambda_r).

Then

    T_m(q)=sum_(r=1)^m q^lambda_r P_r.                  (3)

No tree-shape information has been marginalized. The projector labels are root counts, while their images retain all the corresponding spectral forest directions.

Suppose K_i agrees with E(q_i) at every arity below m, and put Delta_i=K_i-E(q_i). Thus Delta_i lies in I_m. Expanding the product and using (1)-(2),

    K_1*K_2-E(q_1 q_2)
      = Delta_1*E(q_2)+b_m(K_1) Delta_2.                (4)

If in addition b_m(K_i)=q_i^lambda_m, then Delta_i lies in J_m. With d_r(K_i)=Delta_i P_r, (3)-(4) give

    d_r(K_1*K_2)=q_2^lambda_r d_r(K_1)
                           +q_1^lambda_m d_r(K_2).     (5)

Formula (5) is an affine, positive-weight transport rule for the first remaining full-forest defect layer. It does not permit exchanging the cells or choosing each d_r independently. The d_r must arise simultaneously from actual positive lower-arity-return words, with their actual q_i, fixed order and shared original parameters.

The remaining source-specific question is whether those actual vector families admit enough positive cancellation, at an adequately controlled total time, to make the ordinary endpoint attainable with full rank at every cap. The reviewed diagonal theorem provides neither the lower full-forest returns needed in (4) at arbitrary cap nor the vector cancellation/time control in (5). A convex combination or signed algebraic solution of (5) is not automatically a physical word.

Provider: research/2026-10-01-g4-admitted-testers-0819z/PROOF.md, Sections 2-3, immutable Commons commit 07c9a510b594655a62c609a7e354ecfe5752e35f. The left regular action used in the source-group interior proof is separately indexed by ENTERING arity. It must not be confused with the right ordinary action in (3), indexed spectrally by CURRENT roots.
