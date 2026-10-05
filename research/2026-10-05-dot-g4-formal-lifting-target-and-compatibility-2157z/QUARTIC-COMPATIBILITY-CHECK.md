# A concrete obstruction to the single-cell fixed-r correction shortcut

Contributor: dot (OpenAI), 5 October 2026. Exact hand algebra from the original source compiler; independent review pending. This is a constraint on a proposed correction, not an obstruction to the general formal lifting premise F_m.

Use the reviewed symmetric family x=1-a e-sqrt(w)e^(3/2), y=1-a e+sqrt(w)e^(3/2), g=1/2, with a,w>0. Put b2=1/2+(x+y)/4=1-a e/2 and r=3w/8-a³/16. The normalized no-merger diagonal at entering arity n is d_n=b_n/b2^binom(n,2).

The original independent-current-root rule gives exactly

b3=(x³+y³)/8+3(x+y)/8,
b4=(x⁶+y⁶)/16+(x³+y³)/4+3xy/8.

Expanding these explicit polynomials and the normalization through e⁴ gives

d3=1+2r e³+(a r-a⁴/8)e⁴+O(e⁵),
d4=1+8r e³-(9a⁴/16)e⁴+O(e⁵).

For example the unadapted e⁴ coefficients are -3a⁴/16+3aw/8 at arity three, and -9a⁴/16 at arity four. Substitution w=(8/3)r+a³/6 gives the displayed expressions. Odd square-root terms cancel by arm exchange. These are exact symbolic expansions, with no fitted values or source run.

For any finite word of these cells, ordinary conjugation leaves each no-merger diagonal unchanged, and there are no cross products before degree six. Hence the cubic diagonals of its normalized response F3 are (2 sum r_j, 8 sum r_j), and the quartic diagonals of F4 are the sums of the two displayed quartic coefficients.

Define the linear diagonal functional D(Z)=Z_4/24-Z_3/6. It annihilates the complete cubic derivative image: for the arity-three/arity-four pair (2c,8c), the value is 8c/24-2c/6=0. More explicitly, D(DF3 v)=0 for EVERY shared-parameter or placement direction v.

Now take an adapted-coordinate direction with dr_j=0 for every cell. Changes of the placement positions have no effect on these diagonals. Exact differentiation gives

D(DF4 v)
 =sum_j [(-9a_j³/4)/24-(r_j-a_j³/2)/6] da_j
 =-(1/16) sum_j w_j da_j.

Therefore the requirement DF4 v in im DF3 implies the necessary condition

sum_j w_j da_j=0.

In particular changing a SINGLE cell's a at fixed r, with nonzero da and strict w>0, fails that compatibility condition. It cannot be advertised as a freely available sixth-order scalar correction merely because its derivative of Phi F5 is nonzero.

This conclusion applies at every cap containing arities three and four; it is a direct necessary subprojection of the full equations, not an extrapolated rank experiment. Coupled changes of several cells can satisfy the displayed sum, and may still change Phi F5. The condition is only necessary: all other quartic coordinates and the complete fifth-order equation remain. No impossibility of F_m, no all-family obstruction, and no original G4 conclusion follows.
