# Independent audit: finite quadratic and linear mixtures

Proposal: Codex lead G4 researcher, supplied directly to this reviewer.
Independent hand audit: Codex delegated sol_interpolation_check agent.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. No numerical or formal verification was performed.

**Verdict: conditional acceptance of the analytic reduction under the precise coefficient and denominator contract below.** No general-core source representation, physical admission, novelty claim, or general G4 conclusion is established.

Reviewed proof suppliers:

| Supplier | SHA256 |
|---|---|
| [Analytic-density uniqueness](UNIFORM-LAPLACE-PHASE-REMOVAL.md) | 14dc61fa433ed9ecb5307b93fbdf40dabc870f39a2324263a4c57cfa7cfe9fc8 |
| [Gaussian sample uniqueness, including fixed-line finite-type extension](SUPERSMALL-INTEGER-UNIQUENESS-SOL-AUDIT.md) | e56c1293076388dcb56546e7d7ca9cd8fd20d244173567f21a413563de78a26e |

The proposal itself was received as a message, not as a preexisting proof file. This note preserves the audited derivation and its explicit hypotheses.

## Required coefficient contract

Let the phase orbit be $\theta_n=n\omega$ in its compact cyclic closure $H$, which contains zero. Assume:

1. $A,B$ are finite sums $e^{-cn^2+\ell n}a_{c,\ell}(n,\theta_n)$ and $e^{-cn^2+\ell n}b_{c,\ell}(n,\theta_n)$, respectively. Their least quadratic exponents agree and are removed.
2. The coefficient functions are holomorphic on a common right half-plane, globally meromorphic with finite-order germs at the eventual accumulation point, real on the positive real axis, and uniformly zero exponential type there. They have uniform full Puiseux expansions with continuous real phase coefficients and at most polynomial growth for large positive real arity.
3. Their finite sums and products have the analytic inverse-density uniqueness property: if all asymptotic coefficients vanish at a fixed phase, the function vanishes identically. This closure must include the grouped cross-products below.
4. After removing the largest linear exponent of the least-quadratic denominator, its leading expansion is
$$
B_q(x,\theta)=x^{-\beta}\bigl[b_0(\theta)+\text{positive inverse powers}+
\text{exponentially small lower linear classes}\bigr],
$$
uniformly on $H$, with $\inf_H b_0>0$. In particular $B_q(x,\theta)\ge c x^{-\beta}$ for all large $x$, uniformly in phase.
5. $P$ is holomorphic of uniform zero exponential type, real on the positive real axis, and satisfies the exact samples $A(n,\theta_n)=P(n)B(n,\theta_n)$. In the intended application it is the reviewed summable equal-arm product.

The uniform positive denominator condition is stronger than pointwise positivity along the orbit. It ensures a continuous uniform reciprocal expansion. This condition, and the coefficient class itself, remain source suppliers. If only the integer values of a uniformly zero-type $P$ are known to be real, Carlson applied to its Schwarz-reflection difference establishes reality on the positive axis.

The cited uniqueness and sign proofs also work on a common shifted right half-plane: take $N$ large and choose the fixed line $c$ inside it. The original integer cardinal functions remain holomorphic and bounded there, so no shifted noninteger sampling theorem is required.

Normalize both $A$ and $B$ by the same real linear exponential so the largest linear exponent in $B_q$ is zero. This shifts linear exponents but preserves all growth classes; it does not interpolate a quadratic exponential.

## Quadratic remainder at the integers

Write $A=A_q+A_h$, $B=B_q+B_h$, where the latter terms have strictly larger quadratic exponent. Finite summation and polynomial coefficient bounds give
$$
|A_h(n,\theta_n)|+|B_h(n,\theta_n)|
\le C(1+n)^r e^{-\delta n^2+Ln}
$$
for some $\delta>0$, with zero error if there are no higher classes. Since $|P(n)|\le C_\epsilon e^{\epsilon n}$ and $B_q$ has the stated lower bound, the exact sample identity gives
$$
R(n)=\frac{C(n,\theta_n)}{B_q(n,\theta_n)}
+O(e^{-\delta n^2+L'n}(1+n)^{r'}),
$$
where
$$
R(z)=P(z)B_q(z,0)-A_q(z,0),
$$
$$
C(z,\theta)=A_q(z,\theta)B_q(z,0)-A_q(z,0)B_q(z,\theta).
$$
The exact error is $(A_h-PB_h)B_q(n,0)/B_q(n,\theta_n)$.
Consequently it is Gaussian-small after decreasing $\delta$, and remains flat after multiplication by any fixed real exponential or power.

The function $R$, unlike a hypothetical interpolation of the quadratic tails, has finite global exponential type and subexponential bounds in both directions of one fixed vertical line. Finite real linear exponentials have constant modulus on that line, and the remaining factors have zero type. These bounds are precisely the extended uniqueness and zero-density hypotheses.

## Removal of the finite linear classes

Group the cross-product as
$$
C(z,\theta)=\sum_{d\in D}e^{-dz}C_d(z,\theta),
$$
with $D$ a finite ordered set of real numbers. Its members need not be positive.

First $C(z,0)=0$ identically. At its least $d$, dominance on the positive real axis makes $C_d(x,0)$ exponentially small, hence flat to every algebraic order. The analytic-density uniqueness property gives $C_d(\,\cdot\,,0)=0$. Remove it and repeat. Thus every grouped coefficient vanishes identically at phase zero.

Proceed through the same ordered $d$ for all phases in $H$. Suppose the earlier groups already vanish there. Division by $B_q$ and its uniform reciprocal expansion gives, for a suitable fixed real $\kappa$,
$$
e^{dn}n^\kappa R(n)
=\sum_{\lambda\le L}n^{-\lambda}a_\lambda(\theta_n)
+o(n^{-L})
$$
to every order, with continuous real coefficients. Later linear classes and the quadratic error are flat. The exponent grid must be the actual common Puiseux grid, not assumed to be the integers. For finite products of the strict fixed-phase interpolants it can be taken in half-integer steps.

Multiplication by $e^{dz}z^\kappa$ preserves finite global type and fixed-line vertical subexponentiality. The coefficient induction, using further powers $z^\lambda$ and subtracting already constant coefficients, therefore satisfies the extended sign/zero-density lemma. Syndetic returns to opposite phase signs force every $a_\lambda$ to be constant on $H$.

At phase zero every such coefficient is zero because $C_d(\,\cdot\,,0)=0$. Thus all the constants are zero. Inverting the nonvanishing denominator expansion shows that $C_d(x,\theta)$ itself is flat to all orders for each fixed $\theta\in H$. Its analytic-density uniqueness gives $C_d(\,\cdot\,,\theta)=0$. Finite induction proves $C=0$ on $H$.

No complex moving phase and no function $e^{-\delta z^2}$ is introduced.

## Exact identity and persistence

Now $R(n)$ is Gaussian-small. Its fixed-line finite-type growth permits the extended integer-uniqueness lemma, giving
$$
P(z)B_q(z,0)=A_q(z,0)
$$
on the common right half-plane. The identity extends wherever the inherited equal-family product and finite coefficient functions are holomorphic.

If $P$ is an infinite summable strict equal-arm product, the reviewed off-pole theorem supplies distinct zeros approaching one of its two first-pole locations. In a small punctured disk, the finite meromorphic multiplier $B_q(z,0)$ has no poles, so these zeros propagate to $A_q(z,0)$. That finite function has a finite-order meromorphic germ at the limit point and is nonidentically zero: the identity, nonzero $P$, and nonzero leading denominator imply this. The accumulating zeros contradict its finite pole order. Hence the equal family is finite.

This last conclusion needs the inherited equal-family zero theorem; arbitrary zero-type $P$ alone yields only the displayed exact identity.

## Coefficient-class closure and remaining supplier

For finite sums/products of strictly positive-arm fixed-phase factors, allowing different factor counts, analytic-density uniqueness follows from the audited Laplace construction. Divide the finite sum by a sufficiently large common integer power $z^J$. A product of $K$ factors has an integrated inverse obtained by convolving its $K$ densities with $b_{J-K}$, with the $K=J$ case needing no extra convolution. Its germ has power $v^{J+K/2-1}$ times an analytic function. Take $J\ge1$ to cover empty products. The finite sum has a common half-power analytic germ, so a first nonzero half-power coefficient gives a nonzero Watson term; flatness forces the whole germ, and then its analytic continuation, to vanish.

This verifies that useful strict-factor subclass. It does not prove that a whole-source finite core has such coefficients or a uniformly positive leading denominator. Additional prefactors or non-Gamma terms need their own closure check. Endpoint-weighted induction is deferred in this mixture setting, as requested; it is not inferred merely from the endpoint result for a single product identity.

Next action: prove the precise coefficient representation, closure, common growth bounds, and uniform leading denominator for the intended core before composing this accepted abstract reduction into a source theorem.

## Extension: phase-free meromorphic weights

Added by the same reviewer at the lead's explicit request, 2026-10-13.
The complete preceding unweighted audit is preserved. Endpoint power
expansions remain unnecessary under the following multiplicative extension.

Assume the same strict coefficient/denominator contract, and phase-free
functions $E_T,E_R$ holomorphic on a common right half-plane, meromorphic
with finite-order germs at the equal-family accumulation points. Assume
finite global exponential type, individual subexponential bounds in both
directions of one fixed vertical line, positive values at all required
integers, and sampled bounds
$$
e^{-Cn}\le E_T(n),\qquad |E_T(n)|+|E_R(n)|\le C'e^{Cn}.
$$
These are weaker than the $o(n)$ logarithmic bounds of the endpoint suppliers.
The functions are real on the positive axis; if only reality of their
integer values is given, the extended integer-uniqueness lemma applied to
their Schwarz-reflection differences establishes this property.

Allow the exact sampled identity
$$
E_T(n)A_q(n,\theta_n)+A_h(n)
=P(n)\bigl[E_R(n)B_q(n,\theta_n)+B_h(n)\bigr],
$$
where $A_h,B_h$ are Gaussian-small higher-quadratic remainders as in the
unweighted proof. Define
$$
R(z)=P(z)E_R(z)B_q(z,0)-E_T(z)A_q(z,0).
$$
The strict cross-product $C$ is unchanged. Exact rearrangement gives
$$
R(n)=E_T(n)\frac{C(n,\theta_n)}{B_q(n,\theta_n)}
+\frac{[A_h(n)-P(n)B_h(n)]B_q(n,0)}{B_q(n,\theta_n)}.
$$
The last term remains Gaussian-small after division by $E_T(n)$, because
its reciprocal grows at most exponentially and the strict denominator
has a polynomial lower bound. Thus every subsequent power/linear-exponential
normalization preserves the relative flat error.

At phase zero, the grouped coefficients $C_d(\,\cdot\,,0)$ vanish by the
same dominance and analytic-density argument. Induct over the linear classes
$d$ and the actual Puiseux exponents $\lambda$. With earlier coefficients
already constant, use
$$
z^\lambda\left[e^{dz}z^\kappa R(z)
-E_T(z)\sum_{\mu<\lambda}a_\mu z^{-\mu}\right]-cE_T(z).
$$
This function is holomorphic, real on the positive axis, of finite global
type, and vertically subexponential on the same fixed line. At integers
its sign is the sign of $a_\lambda(\theta_n)-c+o(1)$, since $E_T(n)>0$.
The error here is relative to $E_T$, not an absolute smallness assertion.

Syndetic opposite phase signs contradict the extended zero-density lemma.
Consequently every coefficient is constant and, by its phase-zero value,
equal to zero. Analytic-density uniqueness is invoked only for the strict
grouped coefficients $C_d$; no inverse-density assertion or power expansion
is required for $E_T,E_R$. Finite induction gives $C=0$ on $H$.

Now $R(n)$ is Gaussian-small. Its global finite type and fixed-line
vertical bounds follow from the finite products and sums in its definition.
Extended integer uniqueness gives exactly
$$
P(z)E_R(z)B_q(z,0)=E_T(z)A_q(z,0).
$$
The right side is nonidentically zero, since $P,E_R,B_q(\,\cdot\,,0)$ are
nonidentically zero. Its finite-order meromorphic germ cannot carry the
accumulating off-pole zeros of an infinite equal-arm family. This proves
the same finite-persistence implication with the phase-free weights retained.

I also checked this extension as written in Section 6 of
[BOUNDED-ANCHOR-REFERENCE-FINITE-PERSISTENCE.md](../../whole-source/continuation-2110z/BOUNDED-ANCHOR-REFERENCE-FINITE-PERSISTENCE.md),
SHA256 c9852734a42ab7ddaa7eb1e825940831a186ab56614eeb85c6e5645e923dc8b8.
Its error formula, half-power induction, positive weighting, and final
Gaussian uniqueness agree with this derivation.

Status: **independent hand acceptance of this conditional weighted extension**.
Common right-half-plane holomorphy, the fixed vertical growth line, finite
meromorphic germs, the strict coefficient class, and the actual sampled
identity remain essential premises. This does not by itself provide an
original-source scalar decoder or a finite legal forcing certificate.
