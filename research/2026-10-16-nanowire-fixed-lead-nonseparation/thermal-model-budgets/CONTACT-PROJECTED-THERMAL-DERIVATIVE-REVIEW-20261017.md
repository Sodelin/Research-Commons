# Contact-projected thermal derivative: sufficient certificate

17 October 2026 UTC. dot (OpenAI), with Nolan. Independent hand derivation for coordinating review. No new numerical search, inverse computation, useful-temperature certificate, publication, or novelty claim.

## Result and source contract

The suggested replacement is valid. Read against FIXED-LEAD-THERMAL-BUDGET-CANDIDATE-17.md (SHA256 5867bfa24df7726366b3c59a261857093041b9d843c0a57cfdd31d2ba1e4eaa4) and thermal-budget-execution/RESULT.json. Keep the same energy-independent Hermitian wire, zero internal dissipation, disjoint endpoint contacts, exact normal leads/contact hopping -tau_z times u=1 meV, and one fixed common field. The saved numerical witness is for the positive 60-site profile at B=2 meV only.

Use dimensionless x=E/u, beta=sqrt(1-x^2/4), Pi=PP*, K=xI-h-(x/2-i beta)Pi, G=K^-1. Throughout a certified invertible window |x|<=W<2, set

    A=P*GP, B=P*G K' GP,
    K'=I-Pi/2-i x Pi/(4 beta),
    S=I-2i beta A.

Differentiating gives A'=-B and S'=-2i beta' A+2i beta B. These are derivatives in the probability-equivalent scattering gauge specified in note17. Energy-dependent channel reference phases do not affect the conductance; they need not satisfy the same derivative estimate.

If a>=sup ||A||_2 and b>=sup ||B||_2 over the entire window, then

    D_contact = W a/(2 beta_W) + 2b,
    |f'(x)| <= L_contact = 2N D_contact,
    beta_W=sqrt(1-W^2/4).

Indeed |beta'|<=W/(4 beta_W), beta<=1, and the reflection incoming-electron columns obey the contraction/Cauchy-Schwarz estimate of note17. In physical energy the Lipschitz constant is L_contact/u. This replaces the global inverse-squared leading term; it does not assume cancellation in B without certifying it. One may safely take the minimum of this bound and the old certified L_W.

The same thermal sufficient condition becomes

    (y+eta+L_contact m1)/alpha + Delta_H < 1,

with alpha,m1 and the separate drift budget exactly as in note17. A positive determinant certificate follows. Uniform field or temperature-dependent Hamiltonian statements require their additional uniform/drift premises.

## Explicit zero-centered interval remainder, using the saved witness

All following norms are operator norms, safely upper-bounded by certified Frobenius norms if convenient. Write G0=K(0)^-1, K0'=I-Pi/2, whose norm is at most 1. Let the saved rational Gaussian matrix Z satisfy

    ||K(0)Z-I||<=e<1, ||Z||<=z.

Then

    M=z/(1-e), epsilon=e M,
    ||G0||<=M, ||G0-Z||<=epsilon.

Calculate the small contact blocks and contact row/column norms from Z, retaining their exact complex cancellations:

    lZ >= ||P*Z||, rZ >= ||ZP||,
    aZ >= ||P*ZP||,
    bZ >= ||P*Z K0' ZP||.

Set

    l=lZ+epsilon, r=rZ+epsilon,
    a0=aZ+epsilon,
    b0=bZ+epsilon(lZ+rZ)+epsilon^2.

These certify ||P*G0||<=l, ||G0P||<=r, ||A(0)||<=a0, ||B(0)||<=b0. The b0 estimate expands G0=Z+(G0-Z) on both sides of K0'; no numerical cancellation in the error terms is assumed.

For q=MW<1 and |x|<=W, note17 gives ||K(x)-K(0)||<=W. The resolvent identities yield

    ||P*G(x)|| <= l/(1-q), ||G(x)P|| <= r/(1-q),
    ||P*(G(x)-G0)|| <= l q/(1-q),
    ||(G(x)-G0)P|| <= r q/(1-q),
    ||A(x)-A(0)|| <= l r W/(1-q).

Also ||K'(x)-K0'||<=W/(4 beta_W). Expanding B(x)-B(0) through the two contact factors proves

    b = b0 + l r [ (1-q)^(-2)-1
                         + W/(4 beta_W (1-q)^2) ]

is a valid uniform upper bound. A valid bound for A is

    a = min( a0+l r W/(1-q), 1/beta_W ).

The second option follows from A=(I-S)/(2i beta) and unitary S. These enclosures rigorously preserve the contact-projected central B value, unlike replacing it immediately by ||G0||^2.

## Available data and remaining work

The existing exact Z, sparse K, residual bound e, norm bound z, and endpoint indexing suffice to compute every displayed quantity with rational squared-norm sums and outward square-root bounds. No new physical assumptions or matrix inverse are needed. Saved provenance:

- inverse_gaussian_integer.json SHA256 3a3e46c5d43f89edddf13895a8d203409b89f2c3a4f3cd8ff5d55e01390975fd;
- scaled_K_rows.json SHA256 71c89f64f5b084daab8bb570ff61ad87705d4b150051a8d5196c56b8309d6d03;
- RESULT.json SHA256 21c3fb460b49d07fdbfb0e1ead390ddc89a93ea5c301b903a180cf72005ca14b;
- original physical certificate: https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/FINITE-PAIR-CERTIFICATE-02.md .

The scalar residual JSON alone does not provide aZ,bZ,lZ,rZ; the saved matrix entries are essential. None of those new block norms was computed in this review. The zero-centered guard still requires W<1/M=rho, so this version does not extend the certified energy window. Its remainder can still be conservative. Wider-window claims require another certified invertibility/enclosure argument, for example validated local centers covering the window. A bound at isolated sampled energies is insufficient.

For an end-to-end model-control test without measured data, reuse f(0)<=f0_upper and 0<=f<=2N to certify f_T<=f0_upper+L_contact m1+2N p. Then bound every allowed measurement by y+eta<=that upper bound+2eta before testing the inequality. Do not posit a favorable warm measurement. No laboratory-temperature improvement is established until the block/remainder and thermal inequalities have actually been evaluated and independently checked.
