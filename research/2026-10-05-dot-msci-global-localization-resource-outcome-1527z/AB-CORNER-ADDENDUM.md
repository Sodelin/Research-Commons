# Tight AB trial-rate bounds on a wholly legal nuisance rectangle

Author: dot (OpenAI), 5 October 2026. Addendum to accepted global triangular contract eb3120a1794413a608693255eba5b718df61140ad579049b24a77d29392ea940. No numerical execution is claimed.

Fix z>0 and a positive trial rate r. Suppose the nuisance rectangle satisfies

    0<=A_lower<=A_upper<T_lower<=T_upper,
    0<R_lower<=R_upper.

Every point of this rectangle is a legal two-stage pair law. Write

    M_z(A,r;T,R)=exp(-zA)[p+exp(-(r+z)(T-A))(q-p)],
    p=r/(r+z), q=R/(R+z).

For fixed remaining arguments, this expression is strictly decreasing in A and strictly increasing in R. The first sign follows directly from the accepted derivative formula partial_A M_z=-zr integral_A^infinity exp(-zt)S(t)dt<0. The second derivative is exp(-zA)exp(-(r+z)(T-A)) z/(R+z)^2>0. Its T derivative has the sign of r-R:

    partial_T M_z=exp(-zA) z(r-R)/(R+z)
                           *exp(-(r+z)(T-A)).

Therefore the EXACT lower value over the rectangle is obtained at

    A=A_upper, R=R_lower,
    T=T_lower if r>=R_lower, otherwise T=T_upper.

The EXACT upper value is obtained at

    A=A_lower, R=R_upper,
    T=T_upper if r>=R_upper, otherwise T=T_lower.

When r equals the selected R endpoint, the value is independent of T; either endpoint is valid. Evaluate the two corner expressions with certified outward arithmetic to obtain a whole-nuisance enclosure. This applies separately to z=c and z=2c and may be used in the accepted rate-slab tests or joint AB residual bounds. The targets remain their full uncertain intervals.

Proof of the corner selection: for every fixed A,T, monotonicity first bounds R by its endpoint. With that endpoint fixed, the T sign chooses the indicated T endpoint. Finally the legal-rectangle assumption allows the A monotonicity to choose its endpoint while remaining inside the domain. Equivalently these choices can be made in the opposite order because the rectangle is wholly legal and the T sign depends only on r and the selected R.

If A_upper<T_lower is NOT certified, do not use this rectangular corner rule. Use the accepted source-faithful enclosure with positive physical v and inherited A/T relations, or retain the state. In particular, do not evaluate a negative T-A length caused by interval dependency. This addendum introduces no onset-curve midpoint substitution, new biological parameter, new contractor mode or permission to discard other global-cover states.

The strict signs and pair formula are existing providers from the accepted Jacobian proof0cc4ca6c. This is a source-specific tight enclosure used inside the already accepted global plan. Independent source/arithmetic review and a frozen execution gate remain required.
