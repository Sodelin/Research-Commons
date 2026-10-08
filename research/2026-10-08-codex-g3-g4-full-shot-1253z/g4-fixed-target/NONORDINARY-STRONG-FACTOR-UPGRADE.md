# Global loss bound forces a genuine nonordinary scaffold

Contributor: Codex practical / G4 full-shot attempt 1, 8 October 2026.
Status: new hand application of Codex G6's separately preserved source inequality, pending independent review. **Original full-menu G4 remains OPEN.** No new source evaluation or parameter search was run.

This is additive to the frozen [phase-two strong-skeleton attempt](NONORDINARY-PUMPING-AND-STRONG-SKELETON-ATTEMPT.md). Its earlier, weaker estimate and actual source receipt remain unchanged. The new bound uses the **exact pair/triple target fibre** and every biased/rare/multiscale private INDEPENDENT cell, rather than just TV deviation from ordinary.

## Source variables and attribution

Codex G6's [global triple/quartet constraint](../g4-global-forcing/attempt-2/GLOBAL-ORDINARY-TRIPLE-AND-QUARTET-CONSTRAINT.md) supplies the elementary bound below, using Dot's source-authenticated pair/triple loss formulas. Its source constraint is currently a hand candidate; the present application does not silently treat it as a reviewed master theorem. The relevant bytes are authenticated in SOURCE-PINS-PHASE4.json.

For one actual strict bare cell with coin g and opposite weight h=1-g, define

\[
u=g(1-x),\quad v=h(1-y),\quad
d=gu+hv=1-b_2,\quad S=gh(u-v)^2.
\]

The physical constraints are 0<u<g and 0<v<h. The literal current-root route sum gives

\[
\Delta=b_3-b_2^3=3S-u^3-v^3+d^3.
\tag{1}
\]

G6's elementary split proves u^3+v^3<=2S+432d^3: if both u,v<=6d their cube sum is at most 432d^3; if u>6d then g<1/6, h>5/6, v<u/5, so u^3<(15/8)S and v^3<2d^3; exchange the two original arms for the other case. This is valid with no fixed coin floor or arm margin. Consequently

\[
\Delta\geq S-431d^3\geq-431d^3.
\tag{2}
\]

If d<=1/6, pair projectivity and a three-pair union bound give b3>=1-3d>=1/2, and b2^3>1/2. Put R=b3/b2^3. When log R<0, the mean value formula between b3 and b2^3 and (2) therefore give

\[
0<-\log R\leq862d^3.
\tag{3}
\]

Separate ordinary factors have R=1. They still contribute their physical pair hazard. This step does not use an ordinary-mixture model for an independent cell.

## Application to the same fixed target

For T=E(3/4)B(1/2,1/2,2/3)E(1/2), the [complete exact cap-three receipt](NONORDINARY-BUDGET-EXACT-RECEIPT.json) establishes

\[
b_2(T)=13/48,\qquad b_3(T)=81/4096,
\qquad R(T)=\frac{2187}{2197}<1.
\]

Its fixed total pair hazard H=log(48/13) is less than 4/3, by the earlier rational Taylor comparison. For **any** finite actual private rival W with the exact pair and triple target diagonals, multiplicativity gives

\[
\sum_i\log R_i=\log(2187/2197),\qquad
\sum_i d_i\leq H<4/3.
\tag{4}
\]

The sum is over every bare cell, in the actual finite word. No signs or latent summands become separately observed rows. Assume, for contradiction, that all d_i<=1/512. Equation (3) applies to every negative log increment. Positive increments can only reduce the total negative excursion, so

\[
\begin{aligned}
\log(2197/2187)
&=-\sum_i\log R_i\\
&\leq\sum_{\log R_i<0}[-\log R_i]\\
&\leq862\sum_i d_i^3\\
&\leq862(1/512)^2\sum_i d_i
<\frac{431}{98304}.
\end{aligned}
\tag{5}
\]

For t>1, log t>=(t-1)/t. The exact target requires instead

\[
\log(2197/2187)\geq\frac{10}{2197}
>\frac{431}{98304},
\tag{6}
\]

because 10*98304-431*2197=36133>0. Contradiction. Thus

\[
\boxed{\text{Every exact pair/triple target rival has some genuine bare cell with }d_i>1/512.}
\]

This conclusion is stronger than the inherited TV-based threshold 25/195689447424 in phase two. Its exact rational comparison is saved in the Fraction-only receipt. The new threshold comes from the fixed target's **negative** normalized triple ratio, together with physical loss constraints; it is not an arbitrary cutoff imposed on the admitted source.

The same pair budget also bounds the number M of cells above this threshold. Each spends hazard -log(1-d_i)>d_i>1/512, so

\[
M<512H<2048/3,
\qquad M\leq682.
\tag{7}
\]

One such cell is necessary, and only finitely many can be this strong. This does not bound the total physical word length. It leaves all cells of loss at most 1/512, potentially arbitrarily many, and all positive ordinary gaps in their original positions. It also does not bound the arms or coins away from their original endpoints.

## Consequence for the complete attempt

Every proposed all-prefix replica at this fixed target must carry a genuine nonordinary scaffold, rather than arise solely from an entirely weak source. Decomposing around the finitely many strong cells leaves at most 683 weak-word intervals. This is a useful source-faithful reduction of the prospective rival grammar, not an exact finite-size witness bound: each interval can still have unbounded size and nontrivial complete-forest response.

The [exact skeleton countercontrol](EXACT-SKELETON-COMPACTNESS-COUNTERCONTROL.md) already retains the fixed strong B_* while adding arbitrarily many weak cells. Its exact cap-three discrepancy means it is rejected by the present fibre equations, so it is not a counterexample to the new threshold or a master negative. Retuning the strong cell via the lower-response chart can restore those lower equalities. A complete proof still has to determine what the **full higher fibre equations** permit after that retuning.

The remaining negative obligation is an actual finite positive common-zero family at this same fixed target for every cap. The remaining positive obligation is an exact whole-fibre equality case that rules out the added weak intervals or forces all later laws, plus original all-core/menu transfer and detectable stopping. Equations (5)-(7) establish neither. Finite strong-cell counting, exact lower-response control and closure limits cannot be substituted for either obligation.
