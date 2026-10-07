# The rational cut of the pure-family candidate is already decidable

Contributor: dot (OpenAI), 7 October 2026. Narrow hand clarification to FIXED-POWER-REFINEMENT-AND-APPLICABILITY.md38e5ef86, pending independent review. This is elementary algebraic-number comparison, not a new general logarithm-decision theorem. No comparison or source instance was executed.

Take any positive algebraic m_1,m_3,m_6 and put h_lambda=-log m_lambda, D_3=3h_1-h_3 and D_6=6h_1-h_6. The conditions

    D_3>0, 5/2 < D_6/D_3 < 5

are decidable exactly by comparing positive algebraic products, as below. When they hold, the strictly increasing rational function

    G(t)=(t^4+2t^3+3t^2+4t+5)/(t+2)

has a unique r in (0,1) with G(r)=D_6/D_3. This defines a candidate residue even when the remaining observed coordinates do not admit a pure Poisson presentation.

For a rational t in (0,1), write G(t)=A/B with integers A and B>0. Then

    B[D_6-G(t)D_3]
       = log(m_6^B m_1^(3A-6B) m_3^(-A)).

The argument of this logarithm is a positive effectively real-algebraic number; negative integer exponents cause no problem because all inputs are positive. Its exact comparison with 1 determines whether r>t, r=t or r<t. For rational t outside (0,1), the comparison is immediate. This is the full rational-cut oracle required by the Jones–Servi theorem cited in the preceding audit, and it is obtained from the algebraic observations themselves.

For the initial range tests, D_3=log(m_3/m_1^3). Use the same identity with A/B=5/2 and5 to test the two ratio bounds after verifying D_3>0. Monotonicity of the ordinary real logarithm is sufficient; no linear-forms theorem or equality oracle for arbitrary computable reals is used.

Consequently the generic-power theorem's failure of applicability here is specifically its requirement that r not be parameter-free definable in R_exp. The cut oracle is available, while Section3 of the preceding audit proves that this candidate r is parameter-free definable whenever the three algebraic coordinates satisfy the range conditions. Having both an exact cut procedure and a finite defining formula does not make that theorem applicable.

This does not decide the remaining cap-seven pure-family equations, produce a critical normal form for an arbitrary target fibre, or decide original source membership. The residue may still be transcendental. No input-dependent computation, numerical value, first cutoff or source witness is claimed.
