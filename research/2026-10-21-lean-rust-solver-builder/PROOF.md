# Hand argument for the proposed acquisition boundary

Evidence tier: hand-derived sufficient algorithm plus exact reference
experiments. No novelty, total acquisition or native refinement theorem.

Let r be1,2 or3, let distinct proposed rational a_i belong to(0,1], and let
e_j=j(j+1)/2 for j=0,...,2r. The input supplies m_j at exactly these exponents.

1. Fix the coefficient of x^(e_(2r)) to1. Solve the2r rational linear
   equations p(a_i)=p'(a_i)=0 for the other2r coefficients. The implementation
   uses exact pivoted elimination with8192-bit reduced-rational intermediate
   bounds. A singular or oversized calculation returns UNKNOWN. It does not
   need a claimed universal interpolation or positivity theorem for soundness.

2. Compute F(x)=product_i(x-a_i), divide p by F^2 with monic exact polynomial
   division, require zero remainder, and independently multiply the quotient
   back. Require every quotient coefficient q_j>=0 and q_0>0. A failed
   sufficient-language test is UNKNOWN, not source nonexistence.

3. For each nonzero q_j, emit
      q_j * x^(j mod2) * (x^floor(j/2) F(x))^2.
   Its expansion is q_j*x^j*F(x)^2. Summing gives p exactly. These are already
   terms of the existing certificate language with right=0 and left=0 or1.
   r<=3 gives degree at most21, at most16 quotient monomials and square length
   at most11, inside the existing level8/term16/square15 limits.

4. Call the UNCHANGED original native checker, which reparses every output
   token, applies its128-bit/80-character rational bound, checks normalization,
   nonzero p, exact weighted-square identity and sum_j c_j*m_j=0. Mismatch or
   output-language exhaustion is UNKNOWN. The transport adapter independently
   calls the pinned original Python checker and binds the original literal
   moment vector before constructing the unchanged check_certificate request.

Consequently, any returned certificate has the existing arithmetic conclusion.
If an actual finite bank has nonnegative weights, values in(0,1], and ALL the
stated moments under ONE fixed law, then its expectation of p is0. Every
positive-weight atom is an exact p-root by the previously compiled
Astra.CommonCertificateKernel.supported_atom_is_root. The existing emitter
supplies the per-certificate arithmetic and conditional-bank statement; new
output compilation is still required.

As an additional HAND observation only: q_0>0 and q_j>=0 make Q(x)>0 for x>=0.
Thus p's positive zeros are exactly the proposed a_i. This sharper r-node
statement is not added to a runtime result or advertised as a compiled receiver.
The existing API continues reporting its conservative2r cap.

Nothing here constructs an admitted graph, preserves all physical/protected
coordinates by construction, computes a general all-source census or proves
original G3 negative termination. A fixed small acquisition cap is not the
arbitrary-finite source class. The CM-T02 general sparse-moment component,
the inherited COMMON finite-determination theorem and the separate missing
typed PMF-to-physical receiver retain their original statements.

## Governing work and novelty boundary

The direct prior is the existing singleton identity
(x-a)^2(x+2a)=x^3-3a^2*x+2a^3 in the accepted kernel and native generator.
The current contribution reuses its exact certificate language and checker.
Confluent interpolation, finite atomic moment methods and weighted-square
certificates are classical; no historical novelty claim is made.
The first broad web search returned mostly ordinary orthogonal-polynomial
references, which do not establish a generalized sparse interpolation claim;
none is treated as proof of this algorithm's completeness. The code instead
checks its complete sufficient identity and returns UNKNOWN outside it.
