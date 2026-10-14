# Fixed-clock obstruction for diagonal-vanishing C1 upper-state energies

Proposed extension: Codex lead G4 researcher.
Proof/check and contributor: Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Status: hand proof submitted for independent review. No actual-prefix cone, full ordinary-return exclusion, finite INDEPENDENT certificate, or general G4 theorem is asserted.

This is a separate extension of [the frozen quadratic reduction](EXACT-NINE-STATE-QUADRATIC-CERTIFICATE-REDUCTION-SOL.md), SHA256 c032a131f1584f0dfeb45744877f625d65b50c1be1251b63c0de30e1ce67d9cc. Its bytes are unchanged. The extension closes the clock-aware escape **within the precise energy template and unrestricted-state premise below**, at any prescribed H>0.

## 1. Exact premise and conclusion

Fix a finite cap m>=9 and H>0. Here H is the ordinary pair-hazard budget, not a bound on the sum of physical arm exposures or calendar durations. Let d=(b_2,...,b_m) be the full positive diagonal vector, including the pair clock tau(d)=-log b_2. Normalize the selected upper states by
\[
a=X/b_7,\qquad b=Y/b_7,\qquad v=V/b_4.
\]
Consider
\[
F_d(a,b,v)=v+P_d(a,b)+\Phi(d).                         \tag{1}
\]
Assume that, for every relevant diagonal d,
- P_d(t,t)=0 for every real t;
- P_d is differentiable at (0,0), with gradient zero there.

C1 regularity suffices. No regularity in d is needed for the argument. The quadratic family
\[
P_d(a,b)=c(d)(a^2-b^2)
\]
is included for arbitrary finite clock-aware coefficients c(d).

Suppose this energy decreases under every genuine cell and positive ordinary append operation along actual prefix diagonals whose pair clock, including that append, is at most H. Crucially the operation inequality must hold for unrestricted upper-state inputs (a,b), and arbitrary v, rather than just the actual forest states producing that diagonal. It is enough to require both signs of upper-state perturbations near (0,0). Finally impose the ordinary-target normalization
\[
\Phi(d(E_H))=\Phi(d(I)).                              \tag{2}
\]

**Conclusion:** these premises are inconsistent. This is an obstruction to the stated energy certificate, not to actual source words.

For the nonlinear extension, the diagonal-vanishing condition is only needed at the finitely many points (l,l) arising from the zero-input tests in the constructed word; global diagonal vanishing is a convenient explicit sufficient hypothesis.

## 2. A strict diagonal-return word inside the prescribed clock

Use the inherited [full-rank ordinary diagonal return theorem](../../../2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md), SHA256 ab700065a7d0ed1a6ef5a680743ecffabdc24728325a1a58b70673d254c41905. At the prescribed pair hazard H/8, it supplies a strict finite word C_0 with exactly ordinary diagonals through m and diagonal differential rank m-1.

Write z=(D_3,...,D_m) for the ordinary-neutral Newton defects. The map from log diagonals to (log b_2,z) is invertible. Therefore the defect map has rank m-2 at C_0. Choose an invertible minor and keep the other source parameters fixed. The inverse-function theorem gives a local continuous section eta -> C_eta of **strict words of the same finite shape**, with
\[
z(C_\eta)=\eta,\qquad \tau(C_\eta)<H/4
\]
for all sufficiently small eta. Shrinking the section preserves every positive source margin. This uses an actual submersion at a strict diagonal return, not a signed or convex correction.

The inherited [exact f-zero cell arcs](../../../2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/ACTUAL-LOWER-SELECTED-CANCELLATION.md), SHA256 ec2ee928996f18c1f6481270eb1d54460b8044a800d6c5b14dae67d687bd9f0f, give strict cells
\[
B_u=B_\sigma(u)=B(1/2,\exp[-u z_\sigma(u)],u),\quad u>0,
\]
with f(B_u)=0 exactly and
\[
h=-12W_\sigma u^4+O(u^5),\quad
e=-3W_\sigma u^4+O(u^5),\quad W_\sigma\ne0.
\]
Consequently
\[
-h+2e=6W_\sigma u^4+O(u^5)\ne0                         \tag{3}
\]
for sufficiently small u. Although one arm survival stays at 1/2, its routing probability tends to zero and the other arm duration tends to zero. For each fixed n, its no-merger diagonal obeys
\[
1\ge p_n(B_u)\ge (1-u)^n\exp[-\lambda_n u z_\sigma(u)]\longrightarrow1,
\]
by the all-roots-on-the-second-arm event. The actual cell kernel also tends to identity at every fixed arity. In particular tau(B_u)->0 and z(B_u)->0 at the fixed finite cap. Both arms and the coin are strict at every realizing u>0.

Choose u such that tau(B_u)<H/4 and eta=-z(B_u) lies in the local section. Put
\[
r=\bigl[H-\tau(B_u)-\tau(C_\eta)\bigr]/3>0,
\]
and form the actual word
\[
W=E_r B_u E_r C_\eta E_r.                            \tag{4}
\]
Existing pads inside C_eta remain strict, and adjacent ordinary pads merge into positive intervals. Defect additivity gives z(W)=0; pair hazard additivity gives tau(W)=H. Newton inversion therefore gives **exactly** d(W)=d(E_H) through m.

Every intermediate pair clock is at most H: each ordinary factor and every strict physical cell contributes positive pair hazard. Word (4) contains the strict f-zero cell (3), all connectors are positive, and its construction obeys the fixed target budget. It is only a diagonal return; no ordinary forest equality is claimed.

## 3. Zero-input tests force every diagonal-potential increment to vanish

The [exact source-state interface](../../../2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md), SHA256 7da5c426153438a70513dc7bf703f5ab77630831d4196bd6e83f718c4f75470f, gives the following bare-cell append at a prefix:
\[
a'=a+l,\quad b'=kb+l,\quad
v'=v+s[(-h+2e)a+hb],
\]
where
\[
k=p_6/p_7,\quad l=b_9f/(b_7p_7),\quad
s=b_7/(b_4p_4)>0.                                   \tag{5}
\]
At the virtual input a=b=0, a'=b'=l and v'=v. Both P terms vanish by the diagonal-vanishing condition. The operation inequality therefore forces
\[
\Phi(d')-\Phi(d)\le0.                                \tag{6}
\]
At the same zero upper-state input, an ordinary append also leaves a=b=v=0 and forces (6).

Apply these zero-input tests at every actual prefix diagonal in (4). They are licensed by the unrestricted-state premise, irrespective of the actual upper-state coordinates of W. Summing (6) and using (2) shows that the sum is zero. Since there are finitely many nonpositive summands, **each** Phi increment is zero, including the one at B_u.

## 4. The f-zero cell leaves an uncancellable linear term

At B_u, l=0 and DeltaPhi=0. Set the input b=0 and perturb a around zero. Equation (5) keeps b'=0 and a'=a. Consequently
\[
F'-F=s(-h+2e)a+
       P_{d'}(a,0)-P_d(a,0)
     =s(-h+2e)a+o(|a|).                              \tag{7}
\]
The coefficient is nonzero by (3), and s>0. Choosing the sign of a to agree with that coefficient makes (7)>0 for sufficiently small |a|. This contradicts local two-sided dissipation.

For the clock-aware isotropic quadratic template, the remainder is simply
\[
[c(d')-c(d)]a^2,
\]
so no choice of finite clock-aware coefficient can cancel the linear term once the diagonal-potential increment is forced to zero. The earlier arbitrary-clock monotonicity argument is not needed.

## 5. Scope

The extension excludes clock-aware coefficients and arbitrary clock-aware potentials only in (1), under its zero-diagonal, zero-gradient and unrestricted-state hypotheses. It does not exclude:
- a certificate on a proved actual-prefix cone, where a=b=0 or both perturbation signs might be unavailable;
- corrections with a nonzero gradient at the upper origin or nonzero values on a=b;
- energies depending on T/U, unselected forest coordinates or a larger history state;
- a general nonlinear target-relative inequality.

The bounded-clock construction is an actual positive source word, but it matches only diagonals. It supplies the diagonal cycle needed to contradict this certificate template, not a full-kernel rival at H. No fixed-cap ordinary no-return theorem or G4 closure follows.


## 6. Zero potential: the quadratic template also fails on actual prefixes

The lead researcher additionally proposed the following actual-prefix test. It is a separate strengthening for
\[
F_d=v+c(d)(a^2-b^2),\qquad \Phi=0,                    \tag{8}
\]
where c is locally bounded near the finite diagonal states used below. This test needs no unrestricted-state assumption and no diagonal return.

Fix a sufficiently weak but **fixed** strict cell B_0 on the inherited exact f-zero arc. It satisfies f_0=0 and e_0!=0. Let its parameters p_{j,0},h_0,e_0 remain fixed throughout the construction.

The same inherited rare-coin source expansion used to build the f-zero arcs gives, for d_0=1/2,
\[
f\bigl(B(1/2,e^{-\epsilon z},\epsilon)\bigr)
=-\frac{2}{15}\eta(z)\epsilon^3+O(\epsilon^4),\qquad
\eta(z)=\frac{3(z-d_0)^2-d_0^3}{2}.
\]
In particular the two strict actual families
\[
U_\epsilon^+=B(1/2,e^{-\epsilon/2},\epsilon),\qquad
U_\epsilon^-=B(1/2,e^{-\epsilon},\epsilon)
\]
have respectively
\[
f(U_\epsilon^+)=\epsilon^3/120+O(\epsilon^4),\qquad
f(U_\epsilon^-)=-\epsilon^3/24+O(\epsilon^4).          \tag{9}
\]
Both tend to identity at every finite arity. Choose the sign of U_epsilon so that f(U_epsilon) has the sign of e_0.

For a fixed L>0 take the genuine strictly padded prefix
\[
P_\epsilon=E_L U_\epsilon E_\epsilon.
\]
Its V is exactly zero. Because the bare U_epsilon has upper entries f,f, exact ordinary transport gives
\[
a_\epsilon=\frac{e^{-15L}f(U_\epsilon)}{p_7(U_\epsilon)},
\quad b_\epsilon=a_\epsilon e^{6\epsilon},
\quad v_\epsilon=0.                                 \tag{10}
\]
Thus a_epsilon has the sign of e_0, is nonzero for small epsilon, and tends to zero; b_epsilon/a_epsilon->1. The prefix diagonal tends to d(E_L).

Append the fixed strict B_0 and a positive trailing ordinary pad E_epsilon, producing another genuine strictly padded word. Since f_0=0, formula (5) has l=0 at B_0. Its V increment, unaffected by the trailing ordinary pad after normalization, is
\[
\Delta v=s_\epsilon
 [2e_0a_\epsilon+h_0(b_\epsilon-a_\epsilon)],
\quad
s_\epsilon\longrightarrow
s_0=e^{-15L}/p_{4,0}>0.                              \tag{11}
\]
The new a remains a_epsilon and the new b is
\(e^{6\epsilon}k_0b_\epsilon\), with \(k_0=p_{6,0}/p_{7,0}\) fixed. Local boundedness of c near d(E_L) and d(E_L B_0) bounds all quadratic energy terms by O(a_epsilon^2). Consequently
\[
F(P_\epsilon B_0E_\epsilon)-F(P_\epsilon)
=2s_0e_0a_\epsilon+o(|a_\epsilon|)>0                 \tag{12}
\]
for all sufficiently small epsilon.

Every parameter and every ordinary pad is strictly positive at each realizing epsilon, and each word uses one tuple across arities. If the pair-hazard budget H is desired, choose L<H/4 and the fixed B_0 with hazard<H/4; the remaining weak-cell hazard and two shrinking pads tend to zero, so both compared words lie below H for sufficiently small epsilon. No bound on the physical length of the rare arm is used.

This establishes a genuine actual-prefix obstruction to (8). Restricting to actual prefixes alone therefore cannot rescue the **zero-potential locally bounded isotropic quadratic template**. A nonzero potential, different correction terms, additional state variables, or a suitable constrained energy of another form remains outside this supplement. Neither compared word is asserted to have ordinary endpoint diagonals or forests.
