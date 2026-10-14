# Positive-gap affine grammar: exact nonordinary return threshold

Construction proposed by Codex lead G4 researcher; independently checked and written by Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Evidence: direct hand proof. This is an abstract grammar corollary, not an admitted coalescent-source example, a historical novelty claim, or a G4 conclusion.

The frozen [affine countermodel](LAWSON-MAXIMAL-EXTENSION-BOUNDARY-SOL-COUNTERMODEL.md), SHA256 bf7b37b777b9dc0c8725dcaf78889e3f11cbee28d44836b4d002be48409fd1bb, remains unchanged. Use
\[
(t,y)(s,z)=(t+s,y+e^{-t}z),\qquad E_t=(t,0),\quad R>0.
\]

Declare two kinds of nonordinary generators:
\[
C_+=\{(t,y):t>0,\ y>0\},\qquad
C_-=\{(t,y):t>R,\ y<0\}.
\]
An actual abstract word is either a positive ordinary edge, or
\[
E_{a_0}C_1E_{a_1}\cdots C_kE_{a_k},
\quad k\ge1,\quad a_i>0,\quad C_i\in C_+\cup C_-.
\]
Thus every connector, external pad, cell time, and cell translation magnitude is strictly positive in its respective parameter chart.

**Exact endpoint image.** This grammar realizes precisely
\[
S_R=\{(t,y):t>0,\ y\ge0\}\cup\{(t,y):t>R,\ y\in\mathbb R\}.
\]
Every word has positive total time. A negative endpoint translation requires at least one negative generator, hence total time exceeds R. Conversely, for y>0 and t>0 choose positive a,b with a+b<t; then
\[
(t,y)=E_a(t-a-b,e^a y)E_b
\]
uses one positive generator. For y<0 and t>R choose a+b<t-R and the same formula uses one negative generator. Points with y=0 are ordinary-only words.

**Exact return criterion.** A word containing at least one nonordinary generator can equal E_H if and only if H>R.

Necessity: its endpoint translation is the sum of cell translations multiplied by positive prefix dilation weights. Because every cell translation is nonzero, a zero sum requires both positive and negative cells. A negative cell alone has time greater than R; every other time and every gap is positive. Therefore H>R.

Sufficiency: given H>R put epsilon=(H-R)/5. The two-cell strictly padded word
\[
E_\epsilon\,(\epsilon,1)\,E_\epsilon\,
(R+\epsilon,-e^{2\epsilon})\,E_\epsilon
\]
has total time R+5 epsilon=H. Its translation is
\[
e^{-\epsilon}-e^{-3\epsilon}e^{2\epsilon}=0.
\]
It therefore equals E_H exactly, with a positive cell, a negative cell, and three strictly positive ordinary gaps.

The set of nonordinary return times is exactly (R,infinity): R is an unattained sharp threshold. Since R is arbitrary, signed-time saturation, primitive two-sided signs, actual regular patches approaching identity, diagonal rank, and affine-convex interior—the properties already verified for this same S_R—give no uniform positive return-time bound. Positive interior and nonordinary return thresholds happen to coincide in this example; this coincidence is not asserted as a general semigroup theorem.
