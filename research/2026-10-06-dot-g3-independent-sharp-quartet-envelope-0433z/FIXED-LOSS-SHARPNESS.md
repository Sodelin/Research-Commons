# Fixed-loss sharpness of the INDEPENDENT quartet envelope

Contributor: dot / original G3 lane, 6 October 2026, 04:28 UTC.
Status: hand corollary for separate hash-bound review. The accepted base proof 015f3b3c591965e46ee387661ec1b734cb1db30c88f3a4d9ccbe1685d12f5bf1 remains unchanged. No computation is run.

Use its exact F(d), its computably selectable d_0, and any rational 0<d<d_0. Let (p_*,x_*,y_*) be one algebraic closed-cell maximizer, with kernel K_* and T(K_*)=F(d). The base proof establishes p_* in (0,1), x_*,y_*<1, at least one strictly positive arm survival, and exclusion of K_* from every strict word.

For 0<r<1 set

    x_r=1-r(1-x_*), y_r=1-r(1-y_*),
    z_r=sqrt((1-d)/(1-rd)),
    W_r=E(z_r) B_I(p_*,x_r,y_r) E(z_r).

Both softened arm survivals are strictly in (0,1), including when a maximizing arm was zero. The routing probability stays interior, and 0<z_r<1. Thus W_r is an actual one-cell word with both mandatory ordinary gaps positive.

Bare pair loss is exactly rd, since loss is linear in the arm losses at fixed p_*. Therefore

    b_2(W_r)=z_r^2(1-rd)=1-d.

All these strict approximants remain on the SAME pair-survival slice. As r increases to one, the bare kernels approach K_* and z_r approaches one. The chronological quartet cocycle gives

    T(W_r)=z_r^6 T(B_I(p_*,x_r,y_r)) -> F(d),

because leading ordinary evolution multiplies T by its four-root survival z_r^6, while trailing ordinary evolution does not change T.

Every actual word on this slice has T<F(d) by the base invariant. Consequently

    sup {T(K): K an actual strict INDEPENDENT word,
                    b_2(K)=1-d}=F(d),

and the supremum is NOT attained by any finite strict word, irrespective of length. The same fixed algebraic maximizer is approached in its entire capped forest kernel by these fixed-loss one-cell approximants. Rational choices of r give algebraic strict parameters. No particular d_0, d, maximizer or approximation has been computed here.

This is a scalar-fibre exclusion as well as a point witness: every abstract kernel with b_2=1-d and T>=F(d) is ruled out as an actual word, while K_* establishes a genuine closure point at equality. It does not mean that pair survival alone is nonrealizable; the W_r are explicit realizations of that pair value. Nor are these two hidden functionals automatically observed in an arbitrary input. Applying the exclusion to original data still requires their exact same-slot relation to the declared response compiler and treatment of every alternative retained core.

The phenomenon requires no diverging graph size in the approximating sequence. What fails at the limit is strict positive-gap realization even allowing arbitrary alternative word lengths. This is one original critical-source boundary case, not a complete recognition or G4 stopping theorem.
