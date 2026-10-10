# Bounded source-assembly interface audit: fixed-real-node critical finiteness

10 October 2026, 15:56 UTC. Read-only review of recommendation `a1af3b0648457fe1d6276e1a70503452c2c802216dcb1b0bb7cd8f3e4ce89d8d`, the six pinned existing modules, the exact two-slice certificates, and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. No source edits or compiler invocation were made by this reviewer.

**Conclusion:** the following route is mathematically robust, including all specialization degree drops. It is conditional on the new coefficient/source identities actually passing the kernel. The arithmetic reviews are not substitutes for those bindings.

## 1. Keep the two nested-polynomial variable roles separate

Fix an arbitrary real r>0; no algebraicity assumption is needed. For projection, use polynomials in p with coefficients in R[q]. Put c_i=normalWeight r i, lambda_i=capSevenExponent i, and

    f_i(p,q)=1+p(q^lambda_i-1),
    P_r(p,q)=sum_i c_i(1-q^lambda_i) product_(j != i) f_j,
    Q0_r(p,q)=sum_i c_i lambda_i q^(lambda_i-1) product_(j != i) f_j.

Thus outer X denotes p and inner X denotes q. Mapping coefficients by `Polynomial.evalRingHom q` must give the existing `criticalProbabilityPolynomial` and `sourceQProbabilityPolynomial` exactly. The latter have existing evaluation lemmas `critical_probability_eval` and `source_q_probability_eval`.

By contrast, each integer certificate at z=3 or5 has outer variable p and inner variable r. Evaluate those coefficients at this fixed real r before identifying them with P_r(p,z), Q_r(p,z). Do not confuse this map with projection-variable evaluation. The existing `fixed_resultant_specialization` has a generic scalar argument named r; that argument is the q-specialization when used for T_r below.

## 2. Construct the correct quotient, with specialization and degree control

The inherited `normal_drift` identity is sum_i c_i lambda_i=0. Since sum lambda_i=56, evaluating Q0_r at p=1 gives

    Q0_r(1,q)=q^55 sum_i c_i lambda_i=0.

This is a polynomial identity over R[q], also at q=0. Define

    Q_r = -(Q0_r /_monic (X-1)).

The minus sign is essential: the exported convention is Q0_r=(1-p)Q_r. Exact pinned APIs in `Algebra/Polynomial/Div.lean`:

- line589, `Polynomial.mul_divByMonic_eq_iff_isRoot`;
- line330, `Polynomial.natDegree_divByMonic`;
- line389, `Polynomial.map_divByMonic` for a monic divisor.

The last API makes quotient specialization valid even if coefficients or degrees drop. Alternatively, mapping the already proved product identity suffices for the critical-root implication.

Each f_i has outer degree at most one, and each erased product has five factors. `natDegree_prod_le` and `natDegree_sum_le_of_forall_le` in `Algebra/Polynomial/BigOperators.lean` give deg_p P_r<=5 and deg_p Q0_r<=5. Monic division gives deg_p Q_r<=4, including Q0_r=0. These upper bounds persist under every coefficient evaluation by `natDegree_map_le`.

## 3. Use the source Bezout certificates; determinant equality is unnecessary

The independently checked certificate identities are

    U_z P_r(.,z)+V_z Q_r(.,z)=D_z(r),
    D_z(r) W_z(r)=K_z E_z(r),

for z=3,5 and K_z nonzero integers; both actual W_z are1. The new Lean source bindings must connect the exported lists to these exact source polynomials, not introduce an assumed equality or substitute an arbitrary polynomial with the same name.

The separate kernel obligations E3=G H3, E5=G H5 and no common real root of H3,H5 imply that E3(r),E5(r) cannot both vanish when G(r) is nonzero. The finite modular certificate supplies the correct characteristic-zero lifting, but its list equations still need kernel results.

For G positivity there is an optional shorter exact route: the concrete 239-entry gCoeffs list has all coefficients nonnegative and coefficient22=24640>0. A general Horner/evaluation nonnegativity lemma plus that coefficient proves G(r)>0 for r>0 directly. This avoids expanding a separate factor-product equality; it does not bypass the E_z=G H_z identities. The older positive factor-product theorem is another valid route if its equality to this exact G is proved.

Choose z with E_z(r) nonzero. Then D_z(r) is nonzero. Divide the displayed Bezout coefficients by this scalar to obtain `IsCoprime` for the specialized P and Q over R[p]. No nonvanishing W hypothesis is needed. These are algebraic witness values, not admitted survival parameters.

## 4. Preserve full P degree at the witness; allow Q to drop

The existing general theorem `critical_probability_coeff_five`, together with `normal_weight_sum`, gives

    coeff_5 P_r(.,z)=-normalMass(r) product_i (1-z^lambda_i).

It is nonzero for r>0 and z=3 or5, since every lambda_i is positive. Combined with the upper bound, P_r(.,z).natDegree=5. The existing convenience theorem `normal_probability_coeff_five_ne_zero` assumes0<q<1 and cannot be applied at these witnesses. Use its general coefficient formula instead.

From coprimality, pinned `Polynomial.resultant_ne_zero` (Resultant/Basic.lean633) gives the natural-degree resultant nonzero. To reach the required padded5,4 determinant, use `resultant_add_right_deg` at line343:

    Res(f,g,m,n+k)=coeff_m(f)^k Res(f,g,m,n).

Set m=5=f.natDegree, n=g.natDegree, k=4-g.natDegree. The coefficient and both factors are nonzero. This is the explicit degree-drop-safe argument. Coprimality alone would not justify an arbitrary doubly padded determinant; if both actual degrees were below the padded ones it could vanish.

Define T_r(q)=Res_p(P_r,Q_r;5,4), a genuine polynomial over R in q. Existing `fixed_resultant_specialization` identifies its evaluation at the chosen witness with the nonzero padded resultant. Hence T_r is nonzero. No exported-resultant determinant expansion is needed on this route.

## 5. Strict critical pairs project into roots of T_r

For a strict pair0<p<1,0<q<1, reuse existing `p_response_zero_iff` and `q_response_zero_iff`. They clear the positive product denominator; the latter also uses p!=0. Together with the existing polynomial-evaluation lemmas they give P_r(p,q)=Q0_r(p,q)=0. Since1-p is nonzero, the quotient identity gives Q_r(p,q)=0.

For this q, both specialized degrees may drop. Use the upper-bound version

    Polynomial.exists_mul_add_mul_eq_C_resultant

at Resultant/Basic.lean875, with m=5,n=4 and the nonzero-size disjunction. It supplies f*u+g*v=C(Res(f,g;5,4)). Evaluating at p proves that padded resultant is zero. Then fixed specialization gives T_r(q)=0. No exact-degree assertion is used at this critical pair.

## 6. Finish with finite fibres only over the strict-set image

Let S be the requested actual critical-pair set in R x R, in order(p,q). `Polynomial.finite_setOfPred_isRoot` (Algebra/Polynomial/Roots.lean140) makes the roots of nonzero T_r finite, so `Prod.snd '' S` is finite by the projection argument.

Use `Set.Finite.of_finite_fibers Prod.snd`, Data/Set/Finite/Lattice.lean234. For q in that image, extract a witnessing pair in S first. This supplies0<q<1. Then existing `normal_probability_polynomial_ne_zero` gives the p-polynomial nonzero, and its root set is finite. The fibre of S at q is contained in the image of that root set under p↦(p,q), hence finite.

Do not assert finite p-fibres for every root of T_r: q=1, for example, makes P identically zero. Such boundary q are outside the strict-set image. The exact image-restricted API avoids that semantic error.

This yields the desired all-real fixed-r finiteness theorem (and in particular the recommended0<r<1 domain). No explicit cardinal bound is needed for this endpoint. The old2495 bound requires additional verified q-degree499 bookkeeping and is a separate optional corollary.

## Acceptance boundary

The route discharges the inherited fixed-node finiteness provider only when all actual source/list identities, quotient and specialization proofs, semantic theorem, imported dependencies and full owned axiom audit pass together. A conditional semantic skeleton is useful for development but cannot be promoted while its arithmetic/source hypotheses remain unclosed. This does not formalize uniform endpoint/count compactness, the compact normalized curve/logarithm argument, effective presentation enumeration or original-source membership.
